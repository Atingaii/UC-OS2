(* Direct InfRules for all eighteen real initializer stores. No execution or
   evaluator oracle is a premise of the stable interface. Not a full function,
   Hook implementation, startup invariant, or termination theorem. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.framework.proof.soundness.
Require CertiOS.framework.proof.simulation.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_tcb_fields_bindings ptcb prio ptos pbos id size ext opt bc bp bs bb bi bz be bo :=
 Alvarenv ptcb (Tptr V293_tcb_type) (bc,0%Z) //\\
 Alvarenv prio Tint8 (bp,0%Z) //\\
 Alvarenv ptos (Tptr Tint32) (bs,0%Z) //\\
 Alvarenv pbos (Tptr Tint32) (bb,0%Z) //\\
 Alvarenv id Tint16 (bi,0%Z) //\\
 Alvarenv size Tint32 (bz,0%Z) //\\
 Alvarenv ext (Tptr Tvoid) (be,0%Z) //\\
 Alvarenv opt Tint16 (bo,0%Z).
Lemma V293_tcb_fields_bindings_env : forall ptcb prio ptos pbos id size ext opt bc bp bs bb bi bz be bo s,
 s |= V293_tcb_fields_bindings ptcb prio ptos pbos id size ext opt bc bp bs bb bi bz be bo ->
 V293_tcb_init_env (getlenv s) ptcb prio ptos pbos id size ext opt bc bp bs bb bi bz be bo.
Proof.
 intros. unfold V293_tcb_fields_bindings in H. unfold V293_tcb_init_env.
 destruct H as (H1&H2&H3&H4&H5&H6&H7&H8).
 destruct H1 as [b1 [E1 [B1 _]]]. inversion B1;subst b1.
 destruct H2 as [b2 [E2 [B2 _]]]. inversion B2;subst b2.
 destruct H3 as [b3 [E3 [B3 _]]]. inversion B3;subst b3.
 destruct H4 as [b4 [E4 [B4 _]]]. inversion B4;subst b4.
 destruct H5 as [b5 [E5 [B5 _]]]. inversion B5;subst b5.
 destruct H6 as [b6 [E6 [B6 _]]]. inversion B6;subst b6.
 destruct H7 as [b7 [E7 [B7 _]]]. inversion B7;subst b7.
 destruct H8 as [b8 [E8 [B8 _]]]. inversion B8;subst b8.
 repeat split;assumption.
Qed.
Lemma V293_raw_cells_frame_env : forall cells R (E : env -> env -> Prop),
 (forall s, s |= R -> E (getgenv s) (getlenv s)) ->
 forall s, s |= V293_rdy_raw_cells cells R -> E (getgenv s) (getlenv s).
Proof.
 induction cells as [ | [[a tp] v] cells IH];intros R E HE s HS;cbn [V293_rdy_raw_cells] in HS.
 - apply HE;exact HS.
 - eapply V293_star_env_r;[apply IH;exact HE|exact HS].
Qed.
Lemma V293_raw_cells_CurLINV : forall cells R li tid,
 (R ==> CurLINV li tid) -> V293_rdy_raw_cells cells R ==> CurLINV li tid.
Proof.
 induction cells as [ | [[a tp] v] cells IH];intros R li tid HR;cbn [V293_rdy_raw_cells].
 - exact HR.
 - apply V293_star_CurLINV_r. apply IH;exact HR.
Qed.

Lemma V293_raw_assign_hoare : forall Spec sd li I r ri tid aop before a tp old after replacement e1 e2 rt R,
 Int.unsigned(Int.repr(snd a))=snd a -> assign_type_match tp rt ->
 (V293_rdy_raw_cells (before++(a,tp,old)::after) R ==>
   Lv e1 @ tp == (fst a,Int.repr(snd a)) //\\ Rv e2 @ rt == replacement) ->
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells (before++(a,tp,old)::after) R)
 (sassign e1 e2)
 (<||aop||> ** V293_rdy_raw_cells (before++(a,tp,replacement)::after) R) tid.
Proof.
 intros Spec sd li I r ri tid aop before a tp old after replacement e1 e2 rt R Offset Match Eval HR.
 eapply conseq_rule with
 (p:=<||aop||> ** (V293_rdy_raw_cells (before++after) R ** Amapsto a tp true old))
 (q:=<||aop||> ** (V293_rdy_raw_cells (before++after) R ** Amapsto a tp true replacement)).
 - apply astar_mono;[intros s HS;exact HS| ]. intros s HS.
   apply V293_rdy_cell_out in HS. apply astar_comm;exact HS.
 - apply astar_mono;[intros s HS;exact HS| ]. intros s HS.
   apply V293_rdy_cell_in. apply astar_comm;exact HS.
 - destruct a as [b off]. cbn [fst snd] in *.
   replace (Amapsto (b,off) tp true old) with
     (Amapsto (b,Int.unsigned(Int.repr off)) tp true old) by (rewrite Offset;reflexivity).
   replace (Amapsto (b,off) tp true replacement) with
     (Amapsto (b,Int.unsigned(Int.repr off)) tp true replacement) by (rewrite Offset;reflexivity).
   eapply assign_rule with (l:=(b,Int.repr off)) (tp2:=rt).
   + exact Match.
   + intros s HS. apply Eval. apply V293_rdy_cell_in. apply astar_comm.
     change (s |= V293_rdy_raw_cells (before++after) R ** Amapsto (b,Int.unsigned(Int.repr off)) tp true old) in HS.
     rewrite Offset in HS. exact HS.
   + apply V293_star_CurLINV_l. apply V293_raw_cells_CurLINV;exact HR.
Qed.

Lemma V293_tcb_fields_raw_env : forall cells R ptcb prio ptos pbos id size ext opt bc bp bs bb bi bz be bo s,
 s |= V293_rdy_raw_cells cells
 (V293_tcb_fields_bindings ptcb prio ptos pbos id size ext opt bc bp bs bb bi bz be bo ** R) ->
 V293_tcb_init_env (getlenv s) ptcb prio ptos pbos id size ext opt bc bp bs bb bi bz be bo.
Proof.
 intros. eapply V293_raw_cells_frame_env with
 (E:=fun ge le => V293_tcb_init_env le ptcb prio ptos pbos id size ext opt bc bp bs bb bi bz be bo);[ |exact H].
 intros st HS. refine (V293_star_env_l _ _
 (fun ge le => V293_tcb_init_env le ptcb prio ptos pbos id size ext opt bc bp bs bb bi bz be bo) _ st HS).
 intros st0 H0. apply V293_tcb_fields_bindings_env;exact H0.
Qed.

Lemma V293_typed_not_undef : forall tp v, rule_type_val_match tp v=true -> v<>Vundef.
Proof. intros tp v Match E. subst v. destruct tp;discriminate. Qed.

Ltac V293_tcb_fields_store n rt value :=
 lazymatch goal with
 | |- InfRules ?Spec ?sd ?li ?I ?r ?ri (<||?aop||> ** V293_rdy_raw_cells ?cells ?R) ?stmt ?q ?tid =>
   let before := eval cbn in (firstn n cells) in
   let cell := eval cbn in (nth n cells ((1%positive,0%Z),Tint8,Vundef)) in
   let after := eval cbn in (skipn (S n) cells) in
   lazymatch cell with (?a,?tp,?old) =>
    let updated := eval cbn [app] in (before++(a,tp,value)::after) in
    let one := ltac:(
      eapply (V293_raw_assign_hoare Spec sd li I r ri tid aop before a tp old after value _ _ rt R);
      [cbn [snd];apply Int.unsigned_repr;lia |
       first [solve [apply eq_int;auto] | solve [apply eq_vptr;do 2 eexists;split;reflexivity] |
        solve [apply eq_tnull;first [left;eexists;reflexivity |right;left;eexists;reflexivity |right;right;reflexivity]]] |
       |apply V293_star_CurLINV_r;assumption]) in
    lazymatch stmt with
    | sseq (sassign _ _) _ =>
      eapply seq_rule with (p':=<||aop||> ** V293_rdy_raw_cells updated R);[one | ]
    | sassign _ _ => one
    end
   end
 end.

Theorem V293_OS_TCBInit_fields_hoare : forall Spec sd li I r ri tid aop R
 ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo bt base
 p top bottom identity size ext options old,
 p<13 -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells
  (V293_tcb_init_old_fields bt base old ++
   V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options)
  (V293_tcb_fields_bindings ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo ** R))
 (V293_TCBInit_fields ptcb prio ptos pbos id stk_size pext opt)
 (<||aop||> ** V293_rdy_raw_cells
  (V293_tcb_init_final_fields bt base p top bottom identity size ext options ++
   V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options)
  (V293_tcb_fields_bindings ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo ** R)) tid.
Proof.
 intros Spec sd li I r ri tid aop R ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo bt base
 p top bottom identity size ext options old Range Base Bound Valid HR.
 destruct Valid as (Vs&Vb&Vi&Vz&Ve&Vo).
 destruct (V293_tcb_init_byte_valid p Range) as (Vp&Vy&Vx&Vby&Vbx).
 destruct (V293_prio_coordinates p Range) as [Yrange Xrange].
 unfold V293_TCBInit_fields,V293_tcb_init_old_fields,V293_tcb_init_input_cells,V293_tcb_init_final_fields.
 cbn [app].
 V293_tcb_fields_store 0 (Tptr Tint32) (top).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  pose proof (V293_tcb_fields_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env.
  destruct Env as (Bc&Bp&Bs&Bb&Bi&Bz&Be&Bo).
  cbn [getlenv get_smem get_lenv] in *.
  V293_tcb_init_read Owned 18 Ptr0.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 1%Z 0%Z (Tptr Tint32) Bc Ptr0 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty0 Addr0].
  V293_tcb_init_read Owned 20 Rhs0.
  split.
  - cbn [sat getsmem]. split;[exact Addr0|exact Ty0].
  - cbn [sat getsmem get_smem]. repeat split;first [assumption | solve [V293_rdy_eval] | discriminate | eapply V293_typed_not_undef;eassumption].
 }
 V293_tcb_fields_store 1 (Tint8) (V293_byteval p).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  pose proof (V293_tcb_fields_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env.
  destruct Env as (Bc&Bp&Bs&Bb&Bi&Bz&Be&Bo).
  cbn [getlenv get_smem get_lenv] in *.
  V293_tcb_init_read Owned 18 Ptr1.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 16%Z 50%Z (Tint8) Bc Ptr1 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty1 Addr1].
  V293_tcb_init_read Owned 19 Rhs1.
  split.
  - cbn [sat getsmem]. split;[exact Addr1|exact Ty1].
  - cbn [sat getsmem get_smem]. repeat split;first [assumption | solve [V293_rdy_eval] | discriminate | eapply V293_typed_not_undef;eassumption].
 }
 V293_tcb_fields_store 2 (Tint8) (Vint32 Int.zero).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  pose proof (V293_tcb_fields_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env.
  destruct Env as (Bc&Bp&Bs&Bb&Bi&Bz&Be&Bo).
  cbn [getlenv get_smem get_lenv] in *.
  V293_tcb_init_read Owned 18 Ptr2.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 14%Z 48%Z (Tint8) Bc Ptr2 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty2 Addr2].
  split.
  - cbn [sat getsmem]. split;[exact Addr2|exact Ty2].
  - cbn [sat getsmem get_smem]. repeat split;first [assumption | solve [V293_rdy_eval] | discriminate | eapply V293_typed_not_undef;eassumption].
 }
 V293_tcb_fields_store 3 (Tint8) (Vint32 Int.zero).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  pose proof (V293_tcb_fields_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env.
  destruct Env as (Bc&Bp&Bs&Bb&Bi&Bz&Be&Bo).
  cbn [getlenv get_smem get_lenv] in *.
  V293_tcb_init_read Owned 18 Ptr3.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 15%Z 49%Z (Tint8) Bc Ptr3 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty3 Addr3].
  split.
  - cbn [sat getsmem]. split;[exact Addr3|exact Ty3].
  - cbn [sat getsmem get_smem]. repeat split;first [assumption | solve [V293_rdy_eval] | discriminate | eapply V293_typed_not_undef;eassumption].
 }
 V293_tcb_fields_store 4 (Tint32) (Vint32 Int.zero).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  pose proof (V293_tcb_fields_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env.
  destruct Env as (Bc&Bp&Bs&Bb&Bi&Bz&Be&Bo).
  cbn [getlenv get_smem get_lenv] in *.
  V293_tcb_init_read Owned 18 Ptr4.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 13%Z 44%Z (Tint32) Bc Ptr4 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty4 Addr4].
  split.
  - cbn [sat getsmem]. split;[exact Addr4|exact Ty4].
  - cbn [sat getsmem get_smem]. repeat split;first [assumption | solve [V293_rdy_eval] | discriminate | eapply V293_typed_not_undef;eassumption].
 }
 V293_tcb_fields_store 5 (Tptr Tvoid) (ext).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  pose proof (V293_tcb_fields_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env.
  destruct Env as (Bc&Bp&Bs&Bb&Bi&Bz&Be&Bo).
  cbn [getlenv get_smem get_lenv] in *.
  V293_tcb_init_read Owned 18 Ptr5.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 2%Z 4%Z (Tptr Tvoid) Bc Ptr5 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty5 Addr5].
  V293_tcb_init_read Owned 24 Rhs5.
  split.
  - cbn [sat getsmem]. split;[exact Addr5|exact Ty5].
  - cbn [sat getsmem get_smem]. repeat split;first [assumption | solve [V293_rdy_eval] | discriminate | eapply V293_typed_not_undef;eassumption].
 }
 V293_tcb_fields_store 6 (Tint32) (size).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  pose proof (V293_tcb_fields_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env.
  destruct Env as (Bc&Bp&Bs&Bb&Bi&Bz&Be&Bo).
  cbn [getlenv get_smem get_lenv] in *.
  V293_tcb_init_read Owned 18 Ptr6.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 4%Z 12%Z (Tint32) Bc Ptr6 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty6 Addr6].
  V293_tcb_init_read Owned 23 Rhs6.
  split.
  - cbn [sat getsmem]. split;[exact Addr6|exact Ty6].
  - cbn [sat getsmem get_smem]. repeat split;first [assumption | solve [V293_rdy_eval] | discriminate | eapply V293_typed_not_undef;eassumption].
 }
 V293_tcb_fields_store 7 (Tptr Tint32) (bottom).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  pose proof (V293_tcb_fields_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env.
  destruct Env as (Bc&Bp&Bs&Bb&Bi&Bz&Be&Bo).
  cbn [getlenv get_smem get_lenv] in *.
  V293_tcb_init_read Owned 18 Ptr7.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 3%Z 8%Z (Tptr Tint32) Bc Ptr7 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty7 Addr7].
  V293_tcb_init_read Owned 21 Rhs7.
  split.
  - cbn [sat getsmem]. split;[exact Addr7|exact Ty7].
  - cbn [sat getsmem get_smem]. repeat split;first [assumption | solve [V293_rdy_eval] | discriminate | eapply V293_typed_not_undef;eassumption].
 }
 V293_tcb_fields_store 8 (Tint16) (options).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  pose proof (V293_tcb_fields_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env.
  destruct Env as (Bc&Bp&Bs&Bb&Bi&Bz&Be&Bo).
  cbn [getlenv get_smem get_lenv] in *.
  V293_tcb_init_read Owned 18 Ptr8.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 5%Z 16%Z (Tint16) Bc Ptr8 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty8 Addr8].
  V293_tcb_init_read Owned 25 Rhs8.
  split.
  - cbn [sat getsmem]. split;[exact Addr8|exact Ty8].
  - cbn [sat getsmem get_smem]. repeat split;first [assumption | solve [V293_rdy_eval] | discriminate | eapply V293_typed_not_undef;eassumption].
 }
 V293_tcb_fields_store 9 (Tint16) (identity).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  pose proof (V293_tcb_fields_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env.
  destruct Env as (Bc&Bp&Bs&Bb&Bi&Bz&Be&Bo).
  cbn [getlenv get_smem get_lenv] in *.
  V293_tcb_init_read Owned 18 Ptr9.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 6%Z 18%Z (Tint16) Bc Ptr9 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty9 Addr9].
  V293_tcb_init_read Owned 22 Rhs9.
  split.
  - cbn [sat getsmem]. split;[exact Addr9|exact Ty9].
  - cbn [sat getsmem get_smem]. repeat split;first [assumption | solve [V293_rdy_eval] | discriminate | eapply V293_typed_not_undef;eassumption].
 }
 V293_tcb_fields_store 10 (Tint8) (Vint32 Int.zero).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  pose proof (V293_tcb_fields_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env.
  destruct Env as (Bc&Bp&Bs&Bb&Bi&Bz&Be&Bo).
  cbn [getlenv get_smem get_lenv] in *.
  V293_tcb_init_read Owned 18 Ptr10.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 21%Z 55%Z (Tint8) Bc Ptr10 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty10 Addr10].
  split.
  - cbn [sat getsmem]. split;[exact Addr10|exact Ty10].
  - cbn [sat getsmem get_smem]. repeat split;first [assumption | solve [V293_rdy_eval] | discriminate | eapply V293_typed_not_undef;eassumption].
 }
 V293_tcb_fields_store 11 (Tint8) (V293_byteval (V293_prio_row p)).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  pose proof (V293_tcb_fields_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env.
  destruct Env as (Bc&Bp&Bs&Bb&Bi&Bz&Be&Bo).
  cbn [getlenv get_smem get_lenv] in *.
  V293_tcb_init_read Owned 18 Ptr11.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 18%Z 52%Z (Tint8) Bc Ptr11 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty11 Addr11].
  V293_tcb_init_read Owned 19 Rhs11.
  destruct (V293_coordinate_rhs_eval ge le M prio bp p Range Bp Rhs11) as (YT11 & XT11 & YV11 & XV11).
  split.
  - cbn [sat getsmem]. split;[exact Addr11|exact Ty11].
  - cbn [sat getsmem get_smem]. repeat split;first [assumption | solve [V293_rdy_eval] | discriminate | eapply V293_typed_not_undef;eassumption].
 }
 V293_tcb_fields_store 12 (Tint8) (V293_byteval (V293_prio_bit p)).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  pose proof (V293_tcb_fields_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env.
  destruct Env as (Bc&Bp&Bs&Bb&Bi&Bz&Be&Bo).
  cbn [getlenv get_smem get_lenv] in *.
  V293_tcb_init_read Owned 18 Ptr12.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 17%Z 51%Z (Tint8) Bc Ptr12 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty12 Addr12].
  V293_tcb_init_read Owned 19 Rhs12.
  destruct (V293_coordinate_rhs_eval ge le M prio bp p Range Bp Rhs12) as (YT12 & XT12 & YV12 & XV12).
  split.
  - cbn [sat getsmem]. split;[exact Addr12|exact Ty12].
  - cbn [sat getsmem get_smem]. repeat split;first [assumption | solve [V293_rdy_eval] | discriminate | eapply V293_typed_not_undef;eassumption].
 }
 V293_tcb_fields_store 13 (Tint8) (V293_byteval (2 ^ V293_prio_row p)).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  pose proof (V293_tcb_fields_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env.
  destruct Env as (Bc&Bp&Bs&Bb&Bi&Bz&Be&Bo).
  cbn [getlenv get_smem get_lenv] in *.
  V293_tcb_init_read Owned 18 Ptr13.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 20%Z 54%Z (Tint8) Bc Ptr13 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty13 Addr13].
  V293_tcb_init_read Owned 11 Coord13.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 18%Z 52%Z Tint8 Bc Ptr13 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [CT13 CA13].
  assert (CV13 : evalval (efield (ederef (evar ptcb)) 18%Z) (ge,le,M)=Some (V293_byteval (V293_prio_row p))).
  { exact (proj2 (V293_tcb_byte_field_eval ge le M ptcb bc bt base 18%Z 52%Z _ Bc Ptr13 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia) Coord13)). }
  destruct (V293_tcb_init_mask_eval ge le M (efield (ederef (evar ptcb)) 18%Z) (V293_prio_row p) ltac:(lia) CT13 CV13) as [MT13 MV13].
  split.
  - cbn [sat getsmem]. split;[exact Addr13|exact Ty13].
  - cbn [sat getsmem get_smem]. repeat split;first [assumption | solve [V293_rdy_eval] | discriminate | eapply V293_typed_not_undef;eassumption].
 }
 V293_tcb_fields_store 14 (Tint8) (V293_byteval (2 ^ V293_prio_bit p)).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  pose proof (V293_tcb_fields_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env.
  destruct Env as (Bc&Bp&Bs&Bb&Bi&Bz&Be&Bo).
  cbn [getlenv get_smem get_lenv] in *.
  V293_tcb_init_read Owned 18 Ptr14.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 19%Z 53%Z (Tint8) Bc Ptr14 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty14 Addr14].
  V293_tcb_init_read Owned 12 Coord14.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 17%Z 51%Z Tint8 Bc Ptr14 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [CT14 CA14].
  assert (CV14 : evalval (efield (ederef (evar ptcb)) 17%Z) (ge,le,M)=Some (V293_byteval (V293_prio_bit p))).
  { exact (proj2 (V293_tcb_byte_field_eval ge le M ptcb bc bt base 17%Z 51%Z _ Bc Ptr14 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia) Coord14)). }
  destruct (V293_tcb_init_mask_eval ge le M (efield (ederef (evar ptcb)) 17%Z) (V293_prio_bit p) ltac:(lia) CT14 CV14) as [MT14 MV14].
  split.
  - cbn [sat getsmem]. split;[exact Addr14|exact Ty14].
  - cbn [sat getsmem get_smem]. repeat split;first [assumption | solve [V293_rdy_eval] | discriminate | eapply V293_typed_not_undef;eassumption].
 }
 V293_tcb_fields_store 15 (Tnull) (Vnull).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  pose proof (V293_tcb_fields_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env.
  destruct Env as (Bc&Bp&Bs&Bb&Bi&Bz&Be&Bo).
  cbn [getlenv get_smem get_lenv] in *.
  V293_tcb_init_read Owned 18 Ptr15.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 9%Z 28%Z (Tcom_ptr 411%Z) Bc Ptr15 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty15 Addr15].
  split.
  - cbn [sat getsmem]. split;[exact Addr15|exact Ty15].
  - cbn [sat getsmem get_smem]. repeat split;first [assumption | solve [V293_rdy_eval] | discriminate | eapply V293_typed_not_undef;eassumption].
 }
 V293_tcb_fields_store 16 (Tnull) (Vnull).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  pose proof (V293_tcb_fields_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env.
  destruct Env as (Bc&Bp&Bs&Bb&Bi&Bz&Be&Bo).
  cbn [getlenv get_smem get_lenv] in *.
  V293_tcb_init_read Owned 18 Ptr16.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 11%Z 36%Z (Tcom_ptr 412%Z) Bc Ptr16 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty16 Addr16].
  split.
  - cbn [sat getsmem]. split;[exact Addr16|exact Ty16].
  - cbn [sat getsmem get_smem]. repeat split;first [assumption | solve [V293_rdy_eval] | discriminate | eapply V293_typed_not_undef;eassumption].
 }
 V293_tcb_fields_store 17 (Tnull) (Vnull).

  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  pose proof (V293_tcb_fields_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env.
  destruct Env as (Bc&Bp&Bs&Bb&Bi&Bz&Be&Bo).
  cbn [getlenv get_smem get_lenv] in *.
  V293_tcb_init_read Owned 18 Ptr17.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 10%Z 32%Z (Tptr Tvoid) Bc Ptr17 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty17 Addr17].
  split.
  - cbn [sat getsmem]. split;[exact Addr17|exact Ty17].
  - cbn [sat getsmem get_smem]. repeat split;first [assumption | solve [V293_rdy_eval] | discriminate | eapply V293_typed_not_undef;eassumption].
Qed.

Theorem V293_OS_TCBInit_fields_semantics : forall Spec sd li I r ri tid aop R
 ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo bt base
 p top bottom identity size ext options old,
 p<13 -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 (R ==> CurLINV li tid) ->
 simulation.RuleSem Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells
  (V293_tcb_init_old_fields bt base old ++
   V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options)
  (V293_tcb_fields_bindings ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo ** R))
 (V293_TCBInit_fields ptcb prio ptos pbos id stk_size pext opt)
 (<||aop||> ** V293_rdy_raw_cells
  (V293_tcb_init_final_fields bt base p top bottom identity size ext options ++
   V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options)
  (V293_tcb_fields_bindings ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo ** R)) tid.
Proof.
 intros Spec sd li I r ri tid aop R ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo bt base
 p top bottom identity size ext options old Range Base Bound Valid HR.
 apply RuleSound. apply V293_OS_TCBInit_fields_hoare;assumption.
Qed.

(* Resource consequence of the same real stores: all old task records survive,
   and the initialized seven fields become a new ready-task record. The task
   map is a specification parameter, not an executed ghost-map mutation. *)
Theorem V293_OS_TCBInit_fields_records_hoare : forall tasks Spec sd li I r ri tid aop R
 ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo bt base
 p top bottom identity size ext options old,
 p<13 -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 get tasks (bt,Int.repr base)=None -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells
  (V293_tcb_init_old_fields bt base old ++
   V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options)
  (V293_tcb_fields_bindings ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo **
   (V293_owned_task_records tasks ** R)))
 (V293_TCBInit_fields ptcb prio ptos pbos id stk_size pext opt)
 (<||aop||> ** (V293_owned_task_records
   (set tasks (bt,Int.repr base) (Int.repr(Z.of_nat p),rdy,Vnull)) **
  V293_rdy_raw_cells (V293_tcb_init_record_remainder bt base top bottom identity size ext options)
   (V293_rdy_raw_cells
    (V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options)
    (V293_tcb_fields_bindings ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo ** R)))) tid.
Proof.
 intros tasks Spec sd li I r ri tid aop R ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo bt base
 p top bottom identity size ext options old Range Base Bound Valid Fresh HR.
 eapply conseq_rule with (q:=<||aop||> ** V293_rdy_raw_cells
  (V293_tcb_init_final_fields bt base p top bottom identity size ext options ++
   V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options)
  (V293_tcb_fields_bindings ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo **
   (V293_owned_task_records tasks ** R)));[intros s HS;exact HS| | ].
 - apply astar_mono;[intros s HS;exact HS| ]. intros s Owned.
   assert (Moved : s |= V293_rdy_raw_cells
    (V293_tcb_init_final_fields bt base p top bottom identity size ext options ++
     V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options)
    (V293_owned_task_records tasks **
     (V293_tcb_fields_bindings ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo ** R))).
   { eapply V293_raw_cells_mono;[ |exact Owned]. intros st HS. clear -HS. sep auto. }
   apply V293_raw_cells_move_frame in Moved. rewrite V293_raw_cells_append in Moved.
   assert (Record : s |= V293_owned_task_records tasks **
    (V293_owned_task_record (bt,Int.repr base) (Int.repr(Z.of_nat p)) rdy Vnull **
     V293_rdy_raw_cells (V293_tcb_init_record_remainder bt base top bottom identity size ext options)
      (V293_rdy_raw_cells
       (V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options)
       (V293_tcb_fields_bindings ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo ** R)))).
   { eapply astar_mono;[intros st HS;exact HS| |exact Moved].
     apply V293_initialized_ready_record;try assumption;lia. }
   apply (V293_task_records_insert tasks (bt,Int.repr base)
    (Int.repr(Z.of_nat p)) rdy Vnull _ Fresh). clear -Record. sep auto.
 - apply V293_OS_TCBInit_fields_hoare;try assumption.
   apply V293_star_CurLINV_r;exact HR.
Qed.

Print Assumptions V293_OS_TCBInit_fields_hoare.
Print Assumptions V293_OS_TCBInit_fields_semantics.
Print Assumptions V293_OS_TCBInit_fields_records_hoare.
