(* Actual configured publication/return via InfRules, not an execution oracle.
   Both old-head cases; disabled-entry critical bracket; no CPU Hook proof. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.soundness.
Require CertiOS.framework.proof.simulation.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_pub_bindings ptcb head group rows counter bc bh bg br bn :=
 Alvarenv ptcb (Tptr V293_tcb_type) (bc,0%Z) //\\
 A_notin_lenv head //\\ Agvarenv head (Tptr V293_tcb_type) (bh,0%Z) //\\
 A_notin_lenv group //\\ Agvarenv group Tint8 (bg,0%Z) //\\
 A_notin_lenv rows //\\ Agvarenv rows (Tarray Tint8 2) (br,0%Z) //\\
 A_notin_lenv counter //\\ Agvarenv counter Tint8 (bn,0%Z).
Definition V293_pub_hstate ptcb head group rows counter bc bh bg br bn cells R aop isr is cs :=
 <||aop||> ** V293_rdy_raw_cells cells
 (OS[isr,false,is,cs] ** (V293_pub_bindings ptcb head group rows counter bc bh bg br bn ** R)).
Lemma V293_pub_bindings_good : forall ptcb head group rows counter bc bh bg br bn,
 GoodFrm (V293_pub_bindings ptcb head group rows counter bc bh bg br bn).
Proof. intros. cbn [V293_pub_bindings GoodFrm]. tauto. Qed.
Lemma V293_pub_bindings_env : forall ptcb head group rows counter bc bh bg br bn s,
 s |= V293_pub_bindings ptcb head group rows counter bc bh bg br bn ->
 V293_pub_env (getgenv s) (getlenv s) ptcb head group rows counter bc bh bg br bn.
Proof.
 intros ptcb head group rows counter bc bh bg br bn s HS.
 destruct HS as (Bc&Nh&Gh&Ng&Gg&Nr&Gr&Nn&Gn).
 destruct Bc as [b [Bc [B _]]]. inversion B;subst b;clear B.
 destruct Gh as [b [Gh [B _]]]. inversion B;subst b;clear B.
 destruct Gg as [b [Gg [B _]]]. inversion B;subst b;clear B.
 destruct Gr as [b [Gr [B _]]]. inversion B;subst b;clear B.
 destruct Gn as [b [Gn [B _]]]. inversion B;subst b;clear B.
 destruct Nh as [Nh _]. destruct Ng as [Ng _]. destruct Nr as [Nr _]. destruct Nn as [Nn _].
 assert (Lh:get (getlenv s) head=None).
 { destruct (get (getlenv s) head) eqn:E;[exfalso;apply Nh;eexists;exact E|reflexivity]. }
 assert (Lg:get (getlenv s) group=None).
 { destruct (get (getlenv s) group) eqn:E;[exfalso;apply Ng;eexists;exact E|reflexivity]. }
 assert (Lr:get (getlenv s) rows=None).
 { destruct (get (getlenv s) rows) eqn:E;[exfalso;apply Nr;eexists;exact E|reflexivity]. }
 assert (Ln:get (getlenv s) counter=None).
 { destruct (get (getlenv s) counter) eqn:E;[exfalso;apply Nn;eexists;exact E|reflexivity]. }
 unfold V293_pub_env. repeat split;assumption.
Qed.
Lemma V293_pub_raw_env : forall cells ptcb head group rows counter bc bh bg br bn R isr is cs s,
 s |= V293_rdy_raw_cells cells
 (OS[isr,false,is,cs] ** (V293_pub_bindings ptcb head group rows counter bc bh bg br bn ** R)) ->
 V293_pub_env (getgenv s) (getlenv s) ptcb head group rows counter bc bh bg br bn.
Proof.
 intros. eapply V293_raw_cells_frame_env with (E:=fun ge le=>
 V293_pub_env ge le ptcb head group rows counter bc bh bg br bn);[ |exact H].
 intros st HS. refine (V293_star_env_r _ _ (fun ge le=>
 V293_pub_env ge le ptcb head group rows counter bc bh bg br bn) _ st HS).
 intros st1 H1. refine (V293_star_env_l _ _ (fun ge le=>
 V293_pub_env ge le ptcb head group rows counter bc bh bg br bn) _ st1 H1).
 intros st2 H2. apply V293_pub_bindings_env;exact H2.
Qed.
Ltac V293_publish_env Owned :=
 pose proof (V293_pub_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env;
 destruct Env as (Bc&Nh&Gh&Ng&Gg&Nr&Gr&Nn&Gn);
 cbn [getlenv getgenv get_smem get_lenv get_genv] in *.
Ltac V293_publish_store n rt value :=
 lazymatch goal with
 | |- InfRules ?Spec ?sd ?li ?I ?r ?ri (<||?aop||> ** V293_rdy_raw_cells ?cells ?R) ?stmt ?q ?tid =>
   let before := eval cbn in (firstn n cells) in
   let cell := eval cbn in (nth n cells ((1%positive,0%Z),Tint8,Vundef)) in
   let after := eval cbn in (skipn (S n) cells) in
   lazymatch cell with (?a,?tp,?old) =>
    let updated := eval cbn [app] in (before++(a,tp,value)::after) in
    let one := ltac:(eapply (V293_raw_assign_hoare Spec sd li I r ri tid aop before a tp old after value _ _ rt R);
     [cbn [snd];first [reflexivity|apply Int.unsigned_repr;lia] |
      first [solve [apply eq_int;auto] | solve [apply eq_vptr;do 2 eexists;split;reflexivity] |
       solve [apply eq_vcomptr;split;first [left;eexists;reflexivity|right;eexists;reflexivity]] |
       solve [apply eq_tnull;first [left;eexists;reflexivity|right;left;eexists;reflexivity|right;right;reflexivity]]] |
      |do 2 apply V293_star_CurLINV_r;assumption]) in
    lazymatch stmt with
    | sseq (sassign _ _) _ => eapply seq_rule with (p':=<||aop||> ** V293_rdy_raw_cells updated R);[one| ]
    | sassign _ _ => one
    end
   end
 end.
Lemma V293_pub_critical_enter : forall Spec sd li I r ri tid aop R cells
 ptcb head group rows counter bc bh bg br bn isr is cs,
 GoodFrm R -> InfRules Spec sd li I r ri
 (V293_pub_hstate ptcb head group rows counter bc bh bg br bn cells R aop isr is cs)
 (sprim encrit)
 (V293_pub_hstate ptcb head group rows counter bc bh bg br bn cells R aop isr is (false::cs)) tid.
Proof.
 intros. unfold V293_pub_hstate. eapply conseq_rule.
 - apply astar_mono;[intros s HS;exact HS|apply V293_raw_cells_move_frame].
 - apply astar_mono;[intros s HS;exact HS|apply V293_raw_cells_unmove_frame].
 - apply encrit2_rule. apply V293_raw_cells_good_frame.
   cbn [GoodFrm]. split;[apply V293_pub_bindings_good|assumption].
Qed.
Lemma V293_pub_critical_exit : forall Spec sd li I r ri tid aop R cells
 ptcb head group rows counter bc bh bg br bn isr is cs,
 GoodFrm R -> InfRules Spec sd li I r ri
 (V293_pub_hstate ptcb head group rows counter bc bh bg br bn cells R aop isr is (false::cs))
 (sprim excrit)
 (V293_pub_hstate ptcb head group rows counter bc bh bg br bn cells R aop isr is cs) tid.
Proof.
 intros. unfold V293_pub_hstate. eapply conseq_rule.
 - apply astar_mono;[intros s HS;exact HS|apply V293_raw_cells_move_frame].
 - apply astar_mono;[intros s HS;exact HS|apply V293_raw_cells_unmove_frame].
 - apply excrit2_rule. apply V293_raw_cells_good_frame.
   cbn [GoodFrm]. split;[apply V293_pub_bindings_good|assumption].
Qed.

Lemma V293_pub_guard_eval : forall ptcb head group rows counter bc bt base bh bg br bn bo obase present y x next prev g row n back R aop isr is cs s,
 s |= (V293_pub_hstate ptcb head group rows counter bc bh bg br bn
 (V293_pub_cells bc bt base bh bg br bn bo obase present y x next prev (V293_pub_old_head present bo obase) g row n back) R aop isr is cs) ->
 evalval (eunop oppsite(V293_task_prio_null_test(evar head))) (getsmem s)=
 Some(Vint32 (if present then Int.one else Int.zero)) /\
 evaltype (eunop oppsite(V293_task_prio_null_test(evar head))) (getsmem s)=Some Tint32.
Proof.
 intros ptcb head group rows counter bc bt base bh bg br bn bo obase present y x next prev g row n back R aop isr is cs s HS.
 assert (Env: V293_pub_env (getgenv s) (getlenv s) ptcb head group rows counter bc bh bg br bn).
 { unfold V293_pub_hstate in HS.
   refine (V293_star_env_r _ _ (fun ge le=> V293_pub_env ge le ptcb head group rows counter bc bh bg br bn) _ s HS).
   intros st H. eapply V293_pub_raw_env;exact H. }
 assert (Read:load (Tptr V293_tcb_type) (getmem s) (bh,0%Z)=Some(V293_pub_old_head present bo obase)).
 { unfold V293_pub_hstate in HS. eapply V293_star_load_r;[ |exact HS]. intros st Owned.
   eapply (V293_rdy_raw_load (V293_pub_cells bc bt base bh bg br bn bo obase present y x next prev (V293_pub_old_head present bo obase) g row n back) _ _ _ _ st).
   - unfold V293_pub_cells;cbn [app]. do 6 right;left;reflexivity.
   - destruct present;reflexivity.
   - exact Owned. }
 destruct Env as (Bc&Nh&Gh&Ng&Gg&Nr&Gr&Nn&Gn).
 destruct s as [[[[[[ge le] M] ir] aux] O] op].
 cbn [getlenv getgenv getmem getsmem get_smem get_lenv get_genv get_mem] in *.
 cbn [V293_task_prio_null_test evalval evaltype get_lenv get_genv get_mem].
 cbv delta [env var memory.ident Modules.ident] in *. rewrite Nh,Gh,Read.
 destruct present;split;reflexivity.
Qed.


Lemma V293_pub_backlink_hoare : forall Spec sd li I r ri tid aop R
 ptcb head group rows counter bc bt base bh bg br bn bo obase present y x g row n back isr is cs,
 (0<=obase)%Z -> (obase+24<=Int.max_unsigned)%Z -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_pub_hstate ptcb head group rows counter bc bh bg br bn
  (V293_pub_cells bc bt base bh bg br bn bo obase present y x
   (V293_pub_old_head present bo obase) Vnull (V293_pub_old_head present bo obase) g row n back)
  R aop isr is cs)
 (sifthen (eunop oppsite(V293_task_prio_null_test(evar head)))
   (sassign(V293_pub_field(evar head) 8%Z)(evar ptcb)))
 (V293_pub_hstate ptcb head group rows counter bc bh bg br bn
  (V293_pub_cells bc bt base bh bg br bn bo obase present y x
   (V293_pub_old_head present bo obase) Vnull (V293_pub_old_head present bo obase) g row n (Vptr(bt,Int.repr base)))
  R aop isr is cs) tid.
Proof.
 intros Spec sd li I r ri tid aop R ptcb head group rows counter bc bt base bh bg br bn bo obase present y x g row n back isr is cs OldBase OldBound HR.
 destruct present.
 - eapply ift_rule with(tp:=Tint32).
   + intros s HS. exists(Vint32 Int.one).
     destruct (V293_pub_guard_eval ptcb head group rows counter bc bt base bh bg br bn bo obase true y x _ _ g row n back R aop isr is cs s HS) as [V T].
     cbn [sat]. split;[exact V| ]. split;[exact T|discriminate].
   + intros s [HS [v [V B]]].
     destruct (V293_pub_guard_eval ptcb head group rows counter bc bt base bh bg br bn bo obase true y x _ _ g row n back R aop isr is cs s HS) as [One _].
     rewrite One in V. inversion V;subst v. discriminate B.
   + eapply conseq_rule.
     * intros s [HS _]. exact HS.
     * intros s HS. exact HS.
     * unfold V293_pub_hstate,V293_pub_cells. cbn [app V293_pub_old_head].
       V293_publish_store 10 (Tptr V293_tcb_type) (Vptr(bt,Int.repr base)).
       intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op]. V293_publish_env Owned.
       V293_tcb_init_read Owned 6 HeadRead. V293_tcb_init_read Owned 0 PtrRead.
       destruct (V293_pub_field_address ge le M (evar head) bo obase 8%Z 24%Z (Tcom_ptr 410%Z)
        ltac:(V293_rdy_eval) ltac:(V293_rdy_eval) eq_refl eq_refl OldBase ltac:(lia) ltac:(lia)) as [Ty Addr].
       split.
       -- cbn [sat getsmem]. split;[exact Addr|exact Ty].
       -- cbn [sat getsmem get_smem]. repeat split;first [assumption|solve[V293_rdy_eval]|discriminate].
 - eapply ift_rule with(tp:=Tint32).
   + intros s HS. exists(Vint32 Int.zero).
     destruct (V293_pub_guard_eval ptcb head group rows counter bc bt base bh bg br bn bo obase false y x _ _ g row n back R aop isr is cs s HS) as [V T].
     cbn [sat]. split;[exact V| ]. split;[exact T|discriminate].
   + intros s [HS _]. exact HS.
   + eapply conseq_rule with(p:=Afalse)(q:=Afalse).
     * intros s [HS [v [V B]]].
       destruct (V293_pub_guard_eval ptcb head group rows counter bc bt base bh bg br bn bo obase false y x _ _ g row n back R aop isr is cs s HS) as [Zero _].
       rewrite Zero in V. inversion V;subst v. discriminate B.
     * intros s HS. contradiction.
     * apply pfalse_rule.
Qed.

Theorem V293_OS_TCBInit_publish_body_hoare : forall Spec sd li I r ri tid aop R
 ptcb head group rows counter bc bt base bh bg br bn bo obase present y x g row n oldnext oldprev oldback isr is cs,
 (0<=base)%Z -> (base+54<=Int.max_unsigned)%Z ->
 (0<=obase)%Z -> (obase+24<=Int.max_unsigned)%Z ->
 y<2 -> x<8 -> g<256 -> row<256 -> n<255 ->
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_pub_hstate ptcb head group rows counter bc bh bg br bn
  (V293_pub_cells bc bt base bh bg br bn bo obase present y x oldnext oldprev
   (V293_pub_old_head present bo obase) g row n oldback) R aop isr is cs)
 (V293_TCB_publish_body ptcb head group rows counter)
 (V293_pub_hstate ptcb head group rows counter bc bh bg br bn
  (V293_pub_cells bc bt base bh bg br bn bo obase present y x
   (V293_pub_old_head present bo obase) Vnull (Vptr(bt,Int.repr base))
   (Nat.setbit g y) (Nat.setbit row x) (S n) (Vptr(bt,Int.repr base))) R aop isr is cs) tid.
Proof.
 intros Spec sd li I r ri tid aop R ptcb head group rows counter bc bt base bh bg br bn bo obase present y x g row n oldnext oldprev oldback isr is cs
 Base Bound OldBase OldBound Y X G Row Count HR.
 destruct (V293_rekey_byte_arithmetic g y G ltac:(lia)) as [_ [GB [_ GE]]].
 destruct (V293_rekey_byte_arithmetic row x Row X) as [_ [RB [_ RE]]].
 destruct (V293_mask_byte_value y ltac:(lia)) as [ByBound ByEq].
 destruct (V293_mask_byte_value x X) as [BxBound BxEq].
 pose proof (V293_byte_type y ltac:(lia)) as Yvalid.
 pose proof (V293_byte_type (2^y) ByBound) as ByValid.
 pose proof (V293_byte_type (2^x) BxBound) as BxValid.
 pose proof (V293_byte_type g G) as OldGvalid.
 pose proof (V293_byte_type row Row) as OldRvalid.
 pose proof (V293_byte_type n ltac:(lia)) as OldNvalid.
 pose proof (V293_byte_type _ GB) as Gvalid.
 pose proof (V293_byte_type _ RB) as Rvalid.
 pose proof (V293_byte_type (S n) ltac:(lia)) as Cvalid.
 assert (HeadValid:rule_type_val_match (Tptr V293_tcb_type) (V293_pub_old_head present bo obase)=true) by(destruct present;reflexivity).
 unfold V293_TCB_publish_body,V293_pub_hstate,V293_pub_cells. cbn [app].
 V293_publish_store 1 (Tptr V293_tcb_type) (V293_pub_old_head present bo obase).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op]. V293_publish_env Owned.
  V293_tcb_init_read Owned 0 PtrRead. V293_tcb_init_read Owned 6 HeadRead.
  destruct (V293_pub_field_address ge le M (evar ptcb) bt base 7%Z 20%Z (Tcom_ptr 410%Z)
   ltac:(V293_rdy_eval) ltac:(V293_rdy_eval) eq_refl eq_refl Base ltac:(lia) ltac:(lia)) as [Ty Addr].
  split.
  - cbn [sat getsmem]. split;[exact Addr|exact Ty].
  - cbn [sat getsmem get_smem]. repeat split;first [assumption|solve[V293_rdy_eval]|discriminate|destruct present;discriminate].
 }
 V293_publish_store 2 (Tnull) (Vnull).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op]. V293_publish_env Owned.
  V293_tcb_init_read Owned 0 PtrRead.
  destruct (V293_pub_field_address ge le M (evar ptcb) bt base 8%Z 24%Z (Tcom_ptr 410%Z)
   ltac:(V293_rdy_eval) ltac:(V293_rdy_eval) eq_refl eq_refl Base ltac:(lia) ltac:(lia)) as [Ty Addr].
  split.
  - cbn [sat getsmem]. split;[exact Addr|exact Ty].
  - cbn [sat getsmem get_smem]. repeat split;try reflexivity;discriminate.
 }
 eapply seq_rule;[apply V293_pub_backlink_hoare;assumption| ].
 unfold V293_pub_hstate,V293_pub_cells. cbn [app].
 V293_publish_store 6 (Tptr V293_tcb_type) (Vptr(bt,Int.repr base)).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op]. V293_publish_env Owned.
  V293_tcb_init_read Owned 0 PtrRead.
  cbn [sat getsmem get_smem]. repeat split;first [solve[V293_rdy_eval]|discriminate].
 }
 V293_publish_store 7 (Tint8) (V293_byteval(Nat.setbit g y)).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op]. V293_publish_env Owned.
  V293_tcb_init_read Owned 0 PtrRead. V293_tcb_init_read Owned 4 ByRead.
  destruct (V293_pub_field_value ge le M (evar ptcb) bt base 20%Z 54%Z Tint8 _
   ltac:(V293_rdy_eval) ltac:(V293_rdy_eval) eq_refl eq_refl Base ltac:(lia) ltac:(lia) ByRead) as [Byt Byv].
  rewrite ByEq in Byv. V293_tcb_init_read Owned 7 GroupRead.
  destruct (V293_task_prio_byte_expr_eval ge le M (evar group) _ g y G ltac:(lia)
   ltac:(V293_rdy_eval) Byt ltac:(V293_rdy_eval) Byv) as [_ [Gty [_ Gval]]].
  cbn [sat getsmem get_smem]. repeat split;first [assumption|solve[V293_rdy_eval]|discriminate|eapply V293_typed_not_undef;eassumption].
 }
 V293_publish_store 8 (Tint8) (V293_byteval(Nat.setbit row x)).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op]. V293_publish_env Owned.
  V293_tcb_init_read Owned 0 PtrRead. V293_tcb_init_read Owned 3 YiRead.
  destruct (V293_pub_field_value ge le M (evar ptcb) bt base 18%Z 52%Z Tint8 _
   ltac:(V293_rdy_eval) ltac:(V293_rdy_eval) eq_refl eq_refl Base ltac:(lia) ltac:(lia) YiRead) as [Yt Yv].
  V293_tcb_init_read Owned 5 BxRead.
  destruct (V293_pub_field_value ge le M (evar ptcb) bt base 19%Z 53%Z Tint8 _
   ltac:(V293_rdy_eval) ltac:(V293_rdy_eval) eq_refl eq_refl Base ltac:(lia) ltac:(lia) BxRead) as [Bxt Bxv].
  rewrite BxEq in Bxv. V293_tcb_init_read Owned 8 RowRead.
  destruct (V293_byte_array_offset_eval ge le M (evar rows) (V293_pub_field(evar ptcb) 18%Z) br 0%Z y _
   ltac:(V293_rdy_eval) ltac:(V293_rdy_eval) Yt Yv ltac:(lia)
   ltac:(change(0+Z.of_nat y<=4294967295)%Z;lia) Y RowRead) as [RowType [RowAddr RowValue]].
  destruct (V293_task_prio_byte_expr_eval ge le M _ _ row x Row X RowType Bxt RowValue Bxv) as [_ [Rty [_ Rval]]].
  cbn [sat getsmem get_smem]. repeat split;first [assumption|discriminate|eapply V293_typed_not_undef;eassumption].
 }
 V293_publish_store 9 (Tint8) (V293_byteval(S n)).
 {
  intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op]. V293_publish_env Owned.
  V293_tcb_init_read Owned 9 CountRead.
  assert (Cv : evalval(ecast(ebinop oplus(ecast(evar counter)Tint32)(econst32 Int.one))Tint8)(ge,le,M)=Some(V293_byteval(S n))).
  { cbn [evalval evaltype get_lenv get_genv get_mem]. cbv delta [env var memory.ident Modules.ident] in *.
    rewrite Nn,Gn. cbn beta iota. rewrite CountRead.
    change(Some(Vint32(Int.modu(Int.add(Int.repr(Z.of_nat n))Int.one)(Int.repr 256)))=Some(Vint32(Int.repr(Z.of_nat(S n))))).
    assert(Sum:Int.add(Int.repr(Z.of_nat n))Int.one=Int.repr(Z.of_nat(S n))).
    { unfold Int.one,Int.add. rewrite !Int.unsigned_repr by(unfold Int.max_unsigned,Int.modulus,Int.wordsize;simpl;lia).
      rewrite Nat2Z.inj_succ. f_equal. }
    rewrite Sum,V293_rekey_byte_narrow by lia. reflexivity. }
  cbn [sat getsmem get_smem]. repeat split;first [assumption|solve[V293_rdy_eval]|discriminate|eapply V293_typed_not_undef;eassumption].
 }
 apply skip_rule.
Qed.

Definition V293_pub_return_post ptcb head group rows counter bc bh bg br bn cells R aop isr is cs : retasrt :=
 fun result => [|result=Some(Vint32 Int.zero)|] **
 V293_pub_hstate ptcb head group rows counter bc bh bg br bn cells R aop isr is cs.

Theorem V293_OS_TCBInit_publish_hoare : forall Spec sd li I tid aop R
 ptcb head group rows counter bc bt base bh bg br bn bo obase present y x g row n oldnext oldprev oldback isr is cs,
 (0<=base)%Z -> (base+54<=Int.max_unsigned)%Z ->
 (0<=obase)%Z -> (obase+24<=Int.max_unsigned)%Z ->
 y<2 -> x<8 -> g<256 -> row<256 -> n<255 -> GoodFrm R ->
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I
 (V293_pub_return_post ptcb head group rows counter bc bh bg br bn
  (V293_pub_cells bc bt base bh bg br bn bo obase present y x
   (V293_pub_old_head present bo obase) Vnull (Vptr(bt,Int.repr base))
   (Nat.setbit g y) (Nat.setbit row x) (S n) (Vptr(bt,Int.repr base))) R aop isr is cs)
 Afalse
 (V293_pub_hstate ptcb head group rows counter bc bh bg br bn
  (V293_pub_cells bc bt base bh bg br bn bo obase present y x oldnext oldprev
   (V293_pub_old_head present bo obase) g row n oldback) R aop isr is cs)
 (V293_TCB_publish ptcb head group rows counter) Afalse tid.
Proof.
 intros. unfold V293_TCB_publish.
 eapply seq_rule;[apply V293_pub_critical_enter;assumption| ].
 eapply seq_rule;[apply V293_OS_TCBInit_publish_body_hoare;assumption| ].
 eapply seq_rule;[apply V293_pub_critical_exit;assumption| ].
 apply rete_rule with(v:=Vint32 Int.zero)(t:=Tint32).
 intros s HS. split.
 - unfold V293_pub_return_post. apply astar_l_apure_intro;[exact HS|reflexivity].
 - destruct s as [[[[[[ge le] M] ir] aux] O] op].
   cbn [sat evalval evaltype getsmem get_smem]. repeat split;try reflexivity;discriminate.
Qed.

Theorem V293_OS_TCBInit_publish_semantics : forall Spec sd li I tid aop R
 ptcb head group rows counter bc bt base bh bg br bn bo obase present y x g row n oldnext oldprev oldback isr is cs,
 (0<=base)%Z -> (base+54<=Int.max_unsigned)%Z ->
 (0<=obase)%Z -> (obase+24<=Int.max_unsigned)%Z ->
 y<2 -> x<8 -> g<256 -> row<256 -> n<255 -> GoodFrm R ->
 (R ==> CurLINV li tid) ->
 simulation.RuleSem Spec sd li I
 (V293_pub_return_post ptcb head group rows counter bc bh bg br bn
  (V293_pub_cells bc bt base bh bg br bn bo obase present y x
   (V293_pub_old_head present bo obase) Vnull (Vptr(bt,Int.repr base))
   (Nat.setbit g y) (Nat.setbit row x) (S n) (Vptr(bt,Int.repr base))) R aop isr is cs)
 Afalse
 (V293_pub_hstate ptcb head group rows counter bc bh bg br bn
  (V293_pub_cells bc bt base bh bg br bn bo obase present y x oldnext oldprev
   (V293_pub_old_head present bo obase) g row n oldback) R aop isr is cs)
 (V293_TCB_publish ptcb head group rows counter) Afalse tid.
Proof. intros. apply RuleSound. apply V293_OS_TCBInit_publish_hoare;assumption. Qed.
