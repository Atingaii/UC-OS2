(* Continuous normalized-prefix execution. No intermediate-memory, evaluator,
   call-result or port-contract premise. Not an execution of raw port calls. *)
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Import ListNotations.
Local Open Scope nat_scope.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Ltac V293_pub_write P H n lhs rhs rt value next step owned :=
  lazymatch type of H with
  | (?ge,?le,?M,?ir,?aux,?O,?op) |= V293_rdy_raw_cells ?cells ?R =>
    let before := eval cbn in (firstn n cells) in
    let cell := eval cbn in (nth n cells ((1%positive,0%Z),Tint8,Vundef)) in
    let after := eval cbn in (skipn (S n) cells) in
    lazymatch cell with (?a,?tp,?old) =>
      let updated := eval cbn [app] in (before++(a,tp,value)::after) in
      let T := fresh "Write" in
      assert (T : exists Mf,
        (forall tail, cstepstar P (curs (sassign lhs rhs),(kenil,tail)) (ge,le,M)
          (curs (sskip None),(kenil,tail)) (ge,le,Mf)) /\
        (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells updated R);
      [eapply (V293_rdy_assign before a tp old after value lhs rhs rt R P ge le M ir aux O op);
       [first [assumption | V293_rdy_eval] | first [assumption | V293_rdy_eval] | cbn [snd];apply Int.unsigned_repr;lia |
        first [assumption | V293_rdy_eval] |
        first [solve [apply eq_int;auto] | solve [apply eq_vptr;do 2 eexists;split;reflexivity] |
          solve [apply eq_vcomptr;split;first [left;eexists;reflexivity | right;eexists;reflexivity]] |
          solve [apply eq_tnull;first [left;eexists;reflexivity | right;left;eexists;reflexivity | right;right;reflexivity]]] |
        first [assumption | V293_rdy_eval] | first [assumption | reflexivity] | exact H] |
       destruct T as (next & step & owned)]
    end
  end.


Definition V293_pub_old_head (present : bool) bo obase : val := if present then Vptr (bo,Int.repr obase) else Vnull.
Definition V293_pub_cells bc bt base bh bg br bn bo obase (present : bool) y x next prev head g r n oldprev
 : list V293_record_cell :=
 [((bc,0%Z),Tptr V293_tcb_type,Vptr (bt,Int.repr base));
  ((bt,(base+20)%Z),Tcom_ptr 410%Z,next);
  ((bt,(base+24)%Z),Tcom_ptr 410%Z,prev);
  ((bt,(base+52)%Z),Tint8,V293_byteval y);
  ((bt,(base+54)%Z),Tint8,V293_byteval (2^y));
  ((bt,(base+53)%Z),Tint8,V293_byteval (2^x));
  ((bh,0%Z),Tptr V293_tcb_type,head);
  ((bg,0%Z),Tint8,V293_byteval g);
  ((br,Z.of_nat y),Tint8,V293_byteval r);
  ((bn,0%Z),Tint8,V293_byteval n)] ++
  if present then [((bo,(obase+24)%Z),Tcom_ptr 410%Z,oldprev)] else nil.
Definition V293_pub_env ge le ptcb head group rows counter bc bh bg br bn :=
 get le ptcb=Some(bc,Tptr V293_tcb_type) /\
 get le head=None /\ get ge head=Some(bh,Tptr V293_tcb_type) /\
 get le group=None /\ get ge group=Some(bg,Tint8) /\
 get le rows=None /\ get ge rows=Some(br,Tarray Tint8 2) /\
 get le counter=None /\ get ge counter=Some(bn,Tint8).

Lemma V293_pub_field_address : forall ge le M pointer bt base tag delta tp,
 evaltype pointer (ge,le,M)=Some (Tptr V293_tcb_type) ->
 evalval pointer (ge,le,M)=Some(Vptr(bt,Int.repr base)) ->
 ftype tag V293_tcb_fields=Some tp -> field_offset tag V293_tcb_fields=Some(Int.repr delta) ->
 (0<=base)%Z -> (0<=delta)%Z -> (base+delta<=Int.max_unsigned)%Z ->
 evaltype (V293_pub_field pointer tag) (ge,le,M)=Some tp /\
 evaladdr (V293_pub_field pointer tag) (ge,le,M)=Some(Vptr(bt,Int.repr(base+delta))).
Proof.
 intros ge le M pointer bt base tag delta tp Ty Value Ft Fo Base Delta Bound.
 assert (Dt : evaltype (ederef pointer) (ge,le,M)=Some V293_tcb_type).
 { cbn [evaltype]. rewrite Ty. reflexivity. }
 unfold V293_pub_field. split.
 - cbn [evaltype]. rewrite Ty. exact Ft.
 - cbn [evaladdr]. rewrite Value. unfold getoff. rewrite Dt.
   cbn [V293_tcb_type]. rewrite Fo. rewrite Int.repr_unsigned. unfold Int.add.
   rewrite !Int.unsigned_repr by lia. reflexivity.
Qed.
Lemma V293_pub_field_value : forall ge le M pointer bt base tag delta tp value,
 evaltype pointer (ge,le,M)=Some (Tptr V293_tcb_type) ->
 evalval pointer (ge,le,M)=Some(Vptr(bt,Int.repr base)) ->
 ftype tag V293_tcb_fields=Some tp -> field_offset tag V293_tcb_fields=Some(Int.repr delta) ->
 (0<=base)%Z -> (0<=delta)%Z -> (base+delta<=Int.max_unsigned)%Z ->
 load tp M (bt,(base+delta)%Z)=Some value ->
 evaltype (V293_pub_field pointer tag) (ge,le,M)=Some tp /\
 evalval (V293_pub_field pointer tag) (ge,le,M)=Some value.
Proof.
 intros ge le M pointer bt base tag delta tp value Ty Value Ft Fo Base Delta Bound Read.
 destruct (V293_pub_field_address ge le M pointer bt base tag delta tp Ty Value Ft Fo Base Delta Bound) as [T A].
 split;[exact T | ]. unfold V293_pub_field in *. cbn [evalval].
 rewrite T. cbn [evaladdr]. rewrite Value. unfold getoff.
 assert (Dt : evaltype (ederef pointer) (ge,le,M)=Some V293_tcb_type).
 { cbn [evaltype]. rewrite Ty. reflexivity. }
 rewrite Dt. cbn [V293_tcb_type]. rewrite Fo. cbn [addrval_to_addr get_mem].
 rewrite Int.repr_unsigned. unfold Int.add.
 rewrite (Int.unsigned_repr base) by lia. rewrite (Int.unsigned_repr delta) by lia.
 rewrite Int.unsigned_repr by lia. exact Read.
Qed.

Theorem V293_OS_TCBInit_publication_execution : forall P ks ge le M ir aux O op R enabled si ci
 ptcb head group rows counter bc bt base bh bg br bn bo obase present y x g r n oldnext oldprev oldback,
 V293_pub_env ge le ptcb head group rows counter bc bh bg br bn ->
 (0<=base)%Z -> (base+54<=Int.max_unsigned)%Z ->
 (0<=obase)%Z -> (obase+24<=Int.max_unsigned)%Z ->
 y<2 -> x<8 -> g<256 -> r<256 -> n<255 ->
 (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_pub_cells bc bt base bh bg br bn bo obase present y x oldnext oldprev
  (V293_pub_old_head present bo obase) g r n oldback) R ->
 exists Mf,
 V293_local_steps P (curs(V293_TCB_publish ptcb head group rows counter),(kenil,ks))
  ((ge,le,M),ir,(enabled,si,ci))
  (curs(srete(econst32 Int.zero)),(kenil,ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
 (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_pub_cells bc bt base bh bg br bn bo obase present y x
  (V293_pub_old_head present bo obase) Vnull (Vptr(bt,Int.repr base))
  (Nat.setbit g y) (Nat.setbit r x) (S n) (Vptr(bt,Int.repr base))) R.
Proof.
 intros P ks ge le M ir aux O op R enabled si ci ptcb head group rows counter
  bc bt base bh bg br bn bo obase present y x g r n oldnext oldprev oldback
  Env Base Bound OldBase OldBound Y X G Row Count Owned.
 destruct Env as (Bc & Nh & Gh & Ng & Gg & Nr & Gr & Nn & Gn).
 destruct (V293_rekey_byte_arithmetic g y G ltac:(lia)) as [_ [GB [_ GE]]].
 destruct (V293_rekey_byte_arithmetic r x Row X) as [_ [RB [_ RE]]].
 destruct (V293_mask_byte_value y ltac:(lia)) as [ByBound _].
 destruct (V293_mask_byte_value x X) as [BxBound _].
 pose proof (V293_byte_type y ltac:(lia)) as Yvalid.
 pose proof (V293_byte_type (2^y) ByBound) as ByValid.
 pose proof (V293_byte_type (2^x) BxBound) as BxValid.
 pose proof (V293_byte_type g G) as OldGvalid.
 pose proof (V293_byte_type r Row) as OldRvalid.
 pose proof (V293_byte_type n ltac:(lia)) as OldNvalid.
 unfold V293_pub_cells in Owned. cbn [app] in Owned.
 V293_tcb_init_read Owned 0 Ptr0.
 destruct (V293_pub_field_address ge le M (evar ptcb) bt base 7%Z 20%Z (Tcom_ptr 410%Z)
  ltac:(V293_rdy_eval) ltac:(V293_rdy_eval) eq_refl eq_refl Base ltac:(lia) ltac:(lia)) as [Tn An].
 assert (HeadPtrValid : rule_type_val_match (Tptr V293_tcb_type) (V293_pub_old_head present bo obase)=true)
  by (destruct present;reflexivity).
 V293_tcb_init_read Owned 6 Head0.
 assert (HeadValid : rule_type_val_match (Tcom_ptr 410%Z) (V293_pub_old_head present bo obase)=true)
  by (destruct present;reflexivity).
 V293_pub_write P Owned 1 (V293_pub_field (evar ptcb) 7%Z) (evar head)
  (Tptr V293_tcb_type) (V293_pub_old_head present bo obase) M1 S1 H1.
 V293_tcb_init_read H1 0 Ptr1.
 destruct (V293_pub_field_address ge le M1 (evar ptcb) bt base 8%Z 24%Z (Tcom_ptr 410%Z)
  ltac:(V293_rdy_eval) ltac:(V293_rdy_eval) eq_refl eq_refl Base ltac:(lia) ltac:(lia)) as [Tp Ap].
 V293_pub_write P H1 2 (V293_pub_field (evar ptcb) 8%Z) enull Tnull Vnull M2 S2 H2.
 assert (Branch : exists M3,
  (forall tail, cstepstar P
   (curs(sifthen (eunop oppsite (V293_task_prio_null_test(evar head)))
     (sassign(V293_pub_field(evar head) 8%Z)(evar ptcb))),(kenil,tail)) (ge,le,M2)
   (curs(sskip None),(kenil,tail)) (ge,le,M3)) /\
  (ge,le,M3,ir,aux,O,op) |= V293_rdy_raw_cells
   (V293_pub_cells bc bt base bh bg br bn bo obase present y x
    (V293_pub_old_head present bo obase) Vnull (V293_pub_old_head present bo obase)
    g r n (Vptr(bt,Int.repr base))) R).
 { destruct present.
   - cbn [V293_pub_old_head] in H2. V293_tcb_init_read H2 6 Head2.
     V293_tcb_init_read H2 0 Ptr2.
     destruct (V293_pub_field_address ge le M2 (evar head) bo obase 8%Z 24%Z (Tcom_ptr 410%Z)
      ltac:(V293_rdy_eval) ltac:(V293_rdy_eval) eq_refl eq_refl OldBase ltac:(lia) ltac:(lia)) as [To Ao].
     V293_pub_write P H2 10 (V293_pub_field(evar head) 8%Z) (evar ptcb)
      (Tptr V293_tcb_type) (Vptr(bt,Int.repr base)) M3 SB H3.
     exists M3. split;[ | exact H3]. intro tail.
     eapply V293_rekey_if_execution with (flag:=true).
     + unfold V293_task_prio_null_test. V293_rdy_eval.
     + intro F. apply SB.
     + discriminate.
   - cbn [V293_pub_old_head] in H2. V293_tcb_init_read H2 6 Head2.
     exists M2. split;[ | exact H2]. intro tail.
     eapply V293_rekey_if_execution with (flag:=false).
     + unfold V293_task_prio_null_test. V293_rdy_eval.
     + discriminate.
     + intros;reflexivity. }
 destruct Branch as (M3 & S3 & H3).
 unfold V293_pub_cells in H3. cbn [app] in H3.
 V293_tcb_init_read H3 0 Ptr3.
 V293_pub_write P H3 6 (evar head) (evar ptcb) (Tptr V293_tcb_type) (Vptr(bt,Int.repr base)) M4 S4 H4.
 V293_tcb_init_read H4 0 Ptr4.
 V293_tcb_init_read H4 4 By4.
 destruct (V293_pub_field_value ge le M4 (evar ptcb) bt base 20%Z 54%Z Tint8 _
  ltac:(V293_rdy_eval) ltac:(V293_rdy_eval) eq_refl eq_refl Base ltac:(lia) ltac:(lia) By4) as [Byt Byv].
 destruct (V293_mask_byte_value y ltac:(lia)) as [_ ByEq]. rewrite ByEq in Byv.
 V293_tcb_init_read H4 7 Group4.
 destruct (V293_task_prio_byte_expr_eval ge le M4 (evar group) _ g y G ltac:(lia)
  ltac:(V293_rdy_eval) Byt ltac:(V293_rdy_eval) Byv) as [_ [Gty [_ Gval]]].
 pose proof (V293_byte_type _ GB) as Gvalid.
 V293_pub_write P H4 7 (evar group) (V293_task_prio_set_expr(evar group)(V293_pub_field(evar ptcb) 20%Z)) Tint8
  (V293_byteval(Nat.setbit g y)) M5 S5 H5.
 V293_tcb_init_read H5 0 Ptr5.
 V293_tcb_init_read H5 3 Yi5.
 destruct (V293_pub_field_value ge le M5 (evar ptcb) bt base 18%Z 52%Z Tint8 _
  ltac:(V293_rdy_eval) ltac:(V293_rdy_eval) eq_refl eq_refl Base ltac:(lia) ltac:(lia) Yi5) as [Yt Yv].
 V293_tcb_init_read H5 5 Bx5.
 destruct (V293_pub_field_value ge le M5 (evar ptcb) bt base 19%Z 53%Z Tint8 _
  ltac:(V293_rdy_eval) ltac:(V293_rdy_eval) eq_refl eq_refl Base ltac:(lia) ltac:(lia) Bx5) as [Bxt Bxv].
 destruct (V293_mask_byte_value x X) as [_ BxEq]. rewrite BxEq in Bxv.
 V293_tcb_init_read H5 8 Row5.
 destruct (V293_byte_array_offset_eval ge le M5 (evar rows) (V293_pub_field(evar ptcb) 18%Z) br 0%Z y _
  ltac:(V293_rdy_eval) ltac:(V293_rdy_eval) Yt Yv ltac:(lia)
  ltac:(change (0+Z.of_nat y<=4294967295)%Z;lia) Y Row5) as [RowType [RowAddr RowValue]].
 destruct (V293_task_prio_byte_expr_eval ge le M5 _ _ r x Row X RowType Bxt RowValue Bxv) as [_ [Rty [_ Rval]]].
 pose proof (V293_byte_type _ RB) as Rvalid.
 V293_pub_write P H5 8 (earrayelem(evar rows)(V293_pub_field(evar ptcb) 18%Z))
  (V293_task_prio_set_expr(earrayelem(evar rows)(V293_pub_field(evar ptcb) 18%Z))(V293_pub_field(evar ptcb) 19%Z))
  Tint8 (V293_byteval(Nat.setbit r x)) M6 S6 H6.
 V293_tcb_init_read H6 9 Count6.
 assert (Cv : evalval (ecast(ebinop oplus(ecast(evar counter) Tint32)(econst32 Int.one)) Tint8)
  (ge,le,M6)=Some(V293_byteval(S n))).
 { cbn [evalval evaltype get_lenv get_genv get_mem]. cbv delta [env var memory.ident Modules.ident] in *.
   rewrite Nn,Gn. cbn beta iota. rewrite Count6.
   change (Some(Vint32(Int.modu (Int.add (Int.repr(Z.of_nat n)) Int.one) (Int.repr 256)))=
    Some(Vint32(Int.repr(Z.of_nat(S n))))).
   assert (Sum : Int.add (Int.repr(Z.of_nat n)) Int.one=Int.repr(Z.of_nat(S n))).
   { unfold Int.one,Int.add. rewrite !Int.unsigned_repr by
      (unfold Int.max_unsigned,Int.modulus,Int.wordsize;simpl;lia).
     rewrite Nat2Z.inj_succ. f_equal. }
   rewrite Sum,V293_rekey_byte_narrow by lia. reflexivity. }
 pose proof (V293_byte_type (S n) ltac:(lia)) as Cvalid.
 V293_pub_write P H6 9 (evar counter) (ecast(ebinop oplus(ecast(evar counter) Tint32)(econst32 Int.one)) Tint8)
  Tint8 (V293_byteval(S n)) Mf S7 H7.
 exists Mf. split;[ | exact H7].
 unfold V293_TCB_publish,V293_TCB_publish_body.
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { apply encrit_step;reflexivity. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_trans. { apply V293_csteps_local. apply S1. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_trans. { apply V293_csteps_local. apply S2. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_trans. { apply V293_csteps_local. apply S3. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_trans. { apply V293_csteps_local. apply S4. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_trans. { apply V293_csteps_local. apply S5. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_trans. { apply V293_csteps_local. apply S6. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_trans. { apply V293_csteps_local. apply S7. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { apply excrit_step;reflexivity. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 apply V293_local_refl.
Qed.
