(* Real argument evaluation, two fresh parameter objects, native loop and void
   return. R stays in the callee environment; return exposes byte preservation. *)
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia Sorting.Permutation.
Import ListNotations.
Local Open Scope Z_scope.

Definition V293_clr_locals dest size bp bs : env :=
  set (set emp size (bs,Tint16)) dest (bp,Tptr Tint8).
Lemma V293_clr_local_addresses : forall dest size bp bs,
  dest<>size -> Permutation (getaddr (V293_clr_locals dest size bp bs))
    [(bs,Tint16);(bp,Tptr Tint8)].
Proof.
  intros dest size bp bs Different. unfold V293_clr_locals.
  change (Permutation
    (getaddr (EnvMod.set (EnvMod.set EnvMod.emp size (bs,Tint16)) dest (bp,Tptr Tint8)))
    [(bs,Tint16);(bp,Tptr Tint8)]).
  cbn [EnvMod.set EnvMod.lst EnvMod.set' EnvMod.emp EnvMod.emp' getaddr getaddrlist].
  destruct (identspec.blt dest size) eqn:Order.
  - apply perm_swap.
  - rewrite identspec.neq_beq_false by congruence. apply Permutation_refl.
Qed.

Theorem V293_OS_MemClr_call_return : forall values P ks ge caller M ir aux O op R
  f dest size bp bs b off ed es,
  P f=Some (V293_MemClr_function dest size) ->
  dest<>size -> bp<>bs -> fresh M bs -> fresh M bp ->
  evaltype ed (ge,caller,M)=Some (Tptr Tint8) ->
  evalval ed (ge,caller,M)=Some (Vptr (b,Int.repr off)) ->
  evaltype es (ge,caller,M)=Some Tint16 ->
  evalval es (ge,caller,M)=Some (Vint32 (Int.repr (Z.of_nat (length values)))) ->
  Z.of_nat (length values)<=65535 -> 0<=off ->
  off+Z.of_nat (length values)<=Int.max_unsigned ->
  (ge,V293_clr_locals dest size bp bs,M,ir,aux,O,op) |=
    V293_rdy_raw_cells (V293_clr_bytes b off values) R ->
  exists Ms Mf,
    cstepstar P (curs (scall f [ed;es]),(kenil,ks)) (ge,caller,M)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    (ge,V293_clr_locals dest size bp bs,Ms,ir,aux,O,op) |=
      V293_rdy_raw_cells
        (V293_clr_params bp bs b (off+Z.of_nat (length values)) 0 ++
         V293_clr_bytes b off (repeat (Vint32 Int.zero) (length values))) R /\
    (forall c i, c<>bp -> c<>bs -> get Mf (c,i)=get Ms (c,i)) /\
    (forall k, (k<4)%nat -> get Mf (bp,Z.of_nat k)=None) /\
    (forall k, (k<2)%nat -> get Mf (bs,Z.of_nat k)=None).
Proof.
  intros values P ks ge caller M ir aux O op R f dest size bp bs b off ed es
    Program Different Blocks FreshSize FreshDest DestType DestValue SizeType SizeValue Bound Start Limit Frame.
  set (le:=V293_clr_locals dest size bp bs).
  set (n:=Z.of_nat (length values)).
  assert (SizeValid : rule_type_val_match Tint16 (Vint32 (Int.repr n))=true).
  { exact (proj1 (V293_clr_arithmetic n 0 ltac:(unfold n;lia) ltac:(lia)
      ltac:(change (0+1<=4294967295);lia))). }
  pose proof (V293_tick_allocate_frame ge le M ir aux O op bs Tint16 _ FreshSize Frame) as SizeAllocated.
  destruct (V293_tick_raw_slot_update (bs,0) Tint16 Vundef (Vint32 (Int.repr n))
    _ _ _ _ _ _ _ _ SizeValid SizeAllocated) as (M1 & SizeStore & SizeOwned).
  assert (SizeRaw : (ge,le,M1,ir,aux,O,op) |=
    Amapsto (bs,0) Tint16 true (Vint32 (Int.repr n)) **
      V293_rdy_raw_cells (V293_clr_bytes b off values) R).
  { unfold V293_owned_record_cell in SizeOwned. apply astar_assoc_elim in SizeOwned.
    apply astar_l_apure_elim in SizeOwned. tauto. }
  assert (FreshDest1 : fresh M1 bp).
  { intros a i E [v Read];subst a. unfold store in SizeStore.
    assert (Same : get M1 (bp,i)=get M (bp,i)).
    { etransitivity.
      - eapply V293_storebytes_outside;[exact SizeStore | left;exact Blocks].
      - apply V293_success_allocb_outside;left;exact Blocks. }
    apply (FreshDest (bp,i) i eq_refl). exists v. etransitivity;[symmetry;exact Same | exact Read]. }
  pose proof (V293_tick_allocate_frame ge le M1 ir aux O op bp (Tptr Tint8) _ FreshDest1 SizeRaw) as DestAllocated.
  destruct (V293_tick_raw_slot_update (bp,0) (Tptr Tint8) Vundef (Vptr (b,Int.repr off))
    _ _ _ _ _ _ _ _ eq_refl DestAllocated) as (M2 & DestStore & DestOwned).
  assert (Both : (ge,le,M2,ir,aux,O,op) |=
    V293_rdy_raw_cells (V293_clr_cells bp bs b off values) R).
  { unfold V293_owned_record_cell in DestOwned. apply astar_assoc_elim in DestOwned.
    apply astar_l_apure_elim in DestOwned. destruct DestOwned as [_ DestOwned]. exact DestOwned. }
  assert (DestBinding : get le dest=Some (bp,Tptr Tint8)).
  { unfold le,V293_clr_locals. apply map_get_set. }
  assert (SizeBinding : get le size=Some (bs,Tint16)).
  { unfold le,V293_clr_locals. rewrite map_get_set' by congruence. apply map_get_set. }
  set (body:=sseq (V293_clr_loop dest size) sret).
  destruct (V293_OS_MemClr_loop_execution values P (kseq sret (kcall f body caller ks))
    ge le M2 ir aux O op R dest size bp bs b off DestBinding SizeBinding Bound Start Limit Both)
    as (Ms & Loop & Final).
  assert (DestCell : (ge,le,Ms,ir,aux,O,op) |=
    Amapsto (bp,0) (Tptr Tint8) true (Vptr (b,Int.repr (off+n))) ** Atrue).
  { unfold V293_clr_params in Final. cbn [app V293_rdy_raw_cells] in Final. clear -Final. sep auto. }
  assert (SizeCell : (ge,le,Ms,ir,aux,O,op) |=
    Amapsto (bs,0) Tint16 true (Vint32 Int.zero) ** Atrue).
  { unfold V293_clr_params in Final. cbn [app V293_rdy_raw_cells] in Final. clear -Final. sep auto. }
  pose proof (V293_tick_raw_owned_writable _ _ _ _ _ _ _ _ _ _ _ DestCell) as DestWritable.
  pose proof (V293_tick_raw_owned_writable _ _ _ _ _ _ _ _ _ _ _ SizeCell) as SizeWritable.
  pose proof (V293_clr_local_addresses dest size bp bs Different) as Layout.
  assert (ND : NoDup (map fst (getaddr le))).
  { assert (Two : NoDup (bs :: bp :: nil)).
    { constructor;[cbn;intuition congruence | constructor;[cbn;tauto | constructor]]. }
    eapply Permutation_NoDup;[apply Permutation_map;apply Permutation_sym;exact Layout | exact Two]. }
  assert (Writable : forall c tp, In (c,tp) (getaddr le) -> V293_bytes_writable Ms c 0 (typelen tp)).
  { intros c tp Member. apply (Permutation_in (c,tp) Layout) in Member.
    destruct Member as [E | [E | E]];[inversion E;subst | inversion E;subst | contradiction];assumption. }
  destruct (V293_tick_void_return P (kcall f body caller ks) ge le caller Ms f body ks eq_refl ND Writable)
    as (Mf & Return & Preserve & Removed).
  exists Ms. exists Mf. split.
  - eapply c_stepstarn. { eapply stmt_step;[reflexivity | eapply spcall_step;exact DestType]. }
    eapply V293_cstepstar_trans.
    { apply V293_expr_steps;apply evalval_imply_estepstar;exact DestValue. }
    eapply c_stepstarn. { eapply stmt_step;[reflexivity | eapply svfeval_step;exact SizeType]. }
    eapply V293_cstepstar_trans.
    { apply V293_expr_steps;apply evalval_imply_estepstar;exact SizeValue. }
    eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply svfevalnil_step]. }
    eapply c_stepstarn.
    { eapply stmt_step;[reflexivity | ].
      eapply sfexec_step with (d1:=dcons dest (Tptr Tint8) (dcons size Tint16 dnil)) (d2:=dnil);
        [reflexivity | reflexivity | exact Program | repeat split | ].
      change ((if type_val_match Tint16 (Vint32 (Int.repr n)) then true else false)=true).
      change ((if rule_type_val_match Tint16 (Vint32 (Int.repr n)) then true else false)=true).
      rewrite SizeValid;reflexivity. }
    eapply c_stepstarn.
    { eapply stmt_step;[reflexivity | ]. eapply sallocp_step;
        [reflexivity | reflexivity | | apply map_get_set | exact SizeStore].
      exists bs. repeat split;try assumption;try reflexivity.
      intros [v E]. rewrite map_emp_get in E;discriminate. }
    eapply c_stepstarn.
    { eapply stmt_step;[reflexivity | ]. eapply sallocp_step;
        [reflexivity | reflexivity | | exact DestBinding | exact DestStore].
      exists bp. repeat split;try assumption;try reflexivity.
      intros [v E]. rewrite map_get_set' in E by congruence. rewrite map_emp_get in E;discriminate. }
    eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sallocend_step]. }
    eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sseq_step]. }
    eapply V293_cstepstar_trans;[exact Loop | ].
    eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sskip_step]. }
    exact Return.
  - split;[exact Final | ]. split.
    + intros c i Cp Cs. apply Preserve. intro Member.
      apply in_map_iff in Member. destruct Member as ([d tp] & E & Member). cbn in E;subst d.
      apply (Permutation_in (c,tp) Layout) in Member. cbn in Member. intuition congruence.
    + split.
      * intros k K. apply Removed with (Tptr Tint8);[ | exact K].
        eapply Permutation_in;[apply Permutation_sym;exact Layout | right;left;reflexivity].
      * intros k K. apply Removed with Tint16;[ | exact K].
        eapply Permutation_in;[apply Permutation_sym;exact Layout | left;reflexivity].
Qed.
Print Assumptions V293_OS_MemClr_call_return.
