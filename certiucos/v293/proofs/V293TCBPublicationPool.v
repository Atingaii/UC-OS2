(* Physical publication boundary. Full 56-byte ownership is retained, including
   padding and the untouched tail. This is not the task-map/ready invariant. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFreePool.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublishHoare.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBAllocatedFields.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.

(* All bytes other than Next, Prev and the three ready fields. *)
Definition V293_tcb_publication_spare_cells b base : list(addr*type) :=
 [((b,(base+0)%Z),Tptr Tint32);((b,(base+50)%Z),Tint8);
  ((b,(base+48)%Z),Tint8);((b,(base+49)%Z),Tint8);
  ((b,(base+44)%Z),Tint32);((b,(base+4)%Z),Tptr Tvoid);
  ((b,(base+12)%Z),Tint32);((b,(base+8)%Z),Tptr Tint32);
  ((b,(base+16)%Z),Tint16);((b,(base+18)%Z),Tint16);
  ((b,(base+55)%Z),Tint8);((b,(base+51)%Z),Tint8);
  ((b,(base+28)%Z),Tcom_ptr 411%Z);((b,(base+36)%Z),Tcom_ptr 412%Z);
  ((b,(base+32)%Z),Tptr Tvoid);((b,(base+40)%Z),Tint16);
  ((b,(base+42)%Z),Tint8);((b,(base+43)%Z),Tint8)].
Definition V293_tcb_active_payload_cells b base :=
 [((b,(base+52)%Z),Tint8);((b,(base+54)%Z),Tint8);((b,(base+53)%Z),Tint8)] ++
 V293_tcb_publication_spare_cells b base.
Definition V293_tcb_active_payload b base := V293_storage(V293_tcb_active_payload_cells b base).

Ltac V293_publication_layout :=
 lazymatch goal with
 | |- Permutation (@nil _) (@nil _) => constructor
 | |- Permutation ?xs (?x::?ys) =>
   let rec extract before rest :=
    lazymatch rest with
    | x::?tail =>
      eapply Permutation_trans with(l':=x::(before++tail));
      [apply Permutation_sym;apply Permutation_middle|apply perm_skip;cbn[app];V293_publication_layout]
    | ?h::?tail => extract(before++[h])tail
    end
   in extract (@nil(addr*type))xs
 end.

Lemma V293_tcb_active_payload_layout : forall b base,
 Permutation
 (V293_tcb_active_payload_cells b base ++ [((b,(base+24)%Z),Tcom_ptr 410%Z)])
 (V293_tcb_free_payload_cells b base).
Proof.
 intros. unfold V293_tcb_active_payload_cells,V293_tcb_publication_spare_cells,
 V293_tcb_free_payload_cells. cbn[app]. V293_publication_layout.
Qed.

Fixpoint V293_tcb_active_chain (n:nat)(prev head:val) : asrt :=
 match n with
 | O=>[|head=Vnull|]
 | S k=>match head with
   | Vptr(b,off)=>[|(Int.unsigned off+55<=Int.max_unsigned)%Z|] **
      (V293_tcb_active_payload b(Int.unsigned off) **
       (EX next:val,[|rule_type_val_match(Tcom_ptr 410%Z)next=true|] **
        (Amapsto(b,(Int.unsigned off+20)%Z)(Tcom_ptr 410%Z)true next **
         (Amapsto(b,(Int.unsigned off+24)%Z)(Tcom_ptr 410%Z)true prev **
          V293_tcb_active_chain k head next))))
   | _=>Afalse
   end
 end.

(* y<2 makes the selected and unselected cells exactly the two ready rows.
   Count equals the physical chain length, not a task-map cardinality claim. *)
Definition V293_tcb_publication_pool bh bg br bn y n head g row other :=
 Amapsto(bh,0%Z)(Tptr V293_tcb_type)true head **
 (Amapsto(bg,0%Z)Tint8 true(V293_byteval g) **
 (Amapsto(br,Z.of_nat y)Tint8 true(V293_byteval row) **
 (Amapsto(br,Z.of_nat(1-y))Tint8 true(V293_byteval other) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval n) ** V293_tcb_active_chain n Vnull head)))).
Definition V293_tcb_publication_new b base y x next prev :=
 V293_rdy_raw_cells
 ([((b,(base+52)%Z),Tint8,V293_byteval y);
  ((b,(base+54)%Z),Tint8,V293_byteval(2^y));
  ((b,(base+53)%Z),Tint8,V293_byteval(2^x))])
 (V293_storage(V293_tcb_publication_spare_cells b base) **
 (Amapsto(b,(base+20)%Z)(Tcom_ptr 410%Z)true next **
  Amapsto(b,(base+24)%Z)(Tcom_ptr 410%Z)true prev)).
Definition V293_tcb_publication_input ptcb head group rows counter bc bt base bh bg br bn y x n oldhead g row other next prev R aop ir si cs :=
 <||aop||> ** OS[ir,false,si,cs] **
 V293_pub_bindings ptcb head group rows counter bc bh bg br bn **
 Amapsto(bc,0%Z)(Tptr V293_tcb_type)true(Vptr(bt,Int.repr base)) **
 (V293_tcb_publication_new bt base y x next prev **
 (V293_tcb_publication_pool bh bg br bn y n oldhead g row other ** R)).
Definition V293_tcb_publication_output ptcb head group rows counter bc bt base bh bg br bn y n g row other R aop ir si cs :=
 <||aop||> ** OS[ir,false,si,cs] **
 V293_pub_bindings ptcb head group rows counter bc bh bg br bn **
 Amapsto(bc,0%Z)(Tptr V293_tcb_type)true(Vptr(bt,Int.repr base)) **
 (V293_tcb_publication_pool bh bg br bn y n(Vptr(bt,Int.repr base))g row other ** R).
Definition V293_tcb_publication_old_tail (present:bool) k bo obase next :=
 if present then [|rule_type_val_match(Tcom_ptr 410%Z)next=true|] **
 (V293_tcb_active_payload bo obase **
 (Amapsto(bo,(obase+20)%Z)(Tcom_ptr 410%Z)true next **
 V293_tcb_active_chain k(Vptr(bo,Int.repr obase))next)) else Aemp.
Definition V293_tcb_publication_frame bt base br y other present k bo obase next R :=
 V293_storage(V293_tcb_publication_spare_cells bt base) **
 (V293_tcb_publication_old_tail present k bo obase next **
 (Amapsto(br,Z.of_nat(1-y))Tint8 true(V293_byteval other) ** R)).

Lemma V293_tcb_publication_prepare : forall ptcb head group rows counter bc bt base bh bg br bn bo obase (present:bool) k y x g row other next prev R aop ir si cs,
 (0<=obase)%Z -> (obase+55<=Int.max_unsigned)%Z ->
 V293_tcb_publication_input ptcb head group rows counter bc bt base bh bg br bn y x
 (if present then S k else O)(V293_pub_old_head present bo obase)g row other next prev R aop ir si cs ==>
 EX oldnext:val,V293_pub_hstate ptcb head group rows counter bc bh bg br bn
 (V293_pub_cells bc bt base bh bg br bn bo obase present y x next prev
 (V293_pub_old_head present bo obase)g row(if present then S k else O)Vnull)
 (V293_tcb_publication_frame bt base br y other present k bo obase oldnext R)aop ir si cs.
Proof.
 intros ptcb head group rows counter bc bt base bh bg br bn bo obase present k y x g row other next prev R aop ir si cs Base Bound s H.
 destruct present.
 - unfold V293_tcb_publication_input,V293_tcb_publication_pool,V293_pub_old_head in H.
   cbn[V293_tcb_active_chain]in H.
   rewrite Int.unsigned_repr in H by lia. sep normal in H. sep destruct H.
   exists x0. unfold V293_pub_hstate,V293_tcb_publication_frame,V293_tcb_publication_old_tail,
   V293_tcb_publication_new,V293_pub_cells,V293_pub_old_head in *.
   cbn[V293_rdy_raw_cells app]in *;clear -H;sep auto.
 - exists Vnull. unfold V293_tcb_publication_input,V293_tcb_publication_pool,V293_tcb_active_chain,
   V293_pub_hstate,V293_tcb_publication_frame,V293_tcb_publication_old_tail,
   V293_tcb_publication_new,V293_pub_cells,V293_pub_old_head in *.
   cbn[V293_rdy_raw_cells app]in *;clear -H;sep auto.
Qed.

Lemma V293_tcb_publication_payload_fold : forall b base y x,
 y<2 -> x<8 ->
 V293_rdy_raw_cells
 ([((b,(base+52)%Z),Tint8,V293_byteval y);
  ((b,(base+54)%Z),Tint8,V293_byteval(2^y));
  ((b,(base+53)%Z),Tint8,V293_byteval(2^x))])
 (V293_storage(V293_tcb_publication_spare_cells b base)) ==>
 V293_tcb_active_payload b base.
Proof.
 intros b base y x Y X s H.
 pose proof(V293_byte_type y ltac:(lia))as Ty.
 destruct(V293_mask_byte_value y ltac:(lia))as[By _].
 destruct(V293_mask_byte_value x X)as[Bx _].
 pose proof(V293_byte_type(2^y)By)as Tby.
 pose proof(V293_byte_type(2^x)Bx)as Tbx.
 change(s |= V293_storage_cell(b,(base+52)%Z)Tint8 **
 (V293_storage_cell(b,(base+54)%Z)Tint8 **
 (V293_storage_cell(b,(base+53)%Z)Tint8 **
 V293_storage(V293_tcb_publication_spare_cells b base)))).
 unfold V293_storage_cell. sep normal.
 exists(V293_byteval y). exists(V293_byteval(2^y)). exists(V293_byteval(2^x)).
 cbn[V293_rdy_raw_cells]in H;clear -H Ty Tby Tbx;sep auto.
Qed.

Lemma V293_tcb_publication_finish : forall ptcb head group rows counter bc bt base bh bg br bn bo obase (present:bool) k y x g row other oldnext R aop ir si cs,
 (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 (0<=obase)%Z -> (obase+55<=Int.max_unsigned)%Z -> y<2 -> x<8 ->
 V293_pub_hstate ptcb head group rows counter bc bh bg br bn
 (V293_pub_cells bc bt base bh bg br bn bo obase present y x
 (V293_pub_old_head present bo obase)Vnull(Vptr(bt,Int.repr base))
 (Nat.setbit g y)(Nat.setbit row x)(S(if present then S k else O))(Vptr(bt,Int.repr base)))
 (V293_tcb_publication_frame bt base br y other present k bo obase oldnext R)aop ir si cs ==>
 V293_tcb_publication_output ptcb head group rows counter bc bt base bh bg br bn y
 (S(if present then S k else O))(Nat.setbit g y)(Nat.setbit row x)other R aop ir si cs.
Proof.
 intros ptcb head group rows counter bc bt base bh bg br bn bo obase present k y x g row other oldnext R aop ir si cs Base Bound OBase OBound Y X s H.
 unfold V293_pub_hstate,V293_pub_cells,V293_tcb_publication_frame in H.
 cbn[V293_rdy_raw_cells app]in H.
 assert(B:s |= V293_rdy_raw_cells
 ([((bt,(base+52)%Z),Tint8,V293_byteval y);
 ((bt,(base+54)%Z),Tint8,V293_byteval(2^y));
 ((bt,(base+53)%Z),Tint8,V293_byteval(2^x))])
 (V293_storage(V293_tcb_publication_spare_cells bt base)) **
 (<||aop||> ** OS[ir,false,si,cs] ** V293_pub_bindings ptcb head group rows counter bc bh bg br bn **
 Amapsto(bc,0%Z)(Tptr V293_tcb_type)true(Vptr(bt,Int.repr base)) **
 Amapsto(bt,(base+20)%Z)(Tcom_ptr 410%Z)true(V293_pub_old_head present bo obase) **
 Amapsto(bt,(base+24)%Z)(Tcom_ptr 410%Z)true Vnull **
 Amapsto(bh,0%Z)(Tptr V293_tcb_type)true(Vptr(bt,Int.repr base)) **
 Amapsto(bg,0%Z)Tint8 true(V293_byteval(Nat.setbit g y)) **
 Amapsto(br,Z.of_nat y)Tint8 true(V293_byteval(Nat.setbit row x)) **
 Amapsto(bn,0%Z)Tint8 true(V293_byteval(S(if present then S k else O))) **
 ((if present then Amapsto(bo,(obase+24)%Z)(Tcom_ptr 410%Z)true(Vptr(bt,Int.repr base)) else Aemp) **
 V293_tcb_publication_old_tail present k bo obase oldnext **
 Amapsto(br,Z.of_nat(1-y))Tint8 true(V293_byteval other) ** R))).
 { destruct present;cbn[V293_rdy_raw_cells]in *;clear -H;sep auto. }
 eapply astar_mono in B;[ |apply V293_tcb_publication_payload_fold;assumption|intros st HS;exact HS].
 unfold V293_tcb_publication_output,V293_tcb_publication_pool.
 cbn[V293_tcb_active_chain]. rewrite Int.unsigned_repr by lia.
 sep normal. exists(V293_pub_old_head present bo obase).
 destruct present.
 - cbn[V293_pub_old_head V293_tcb_active_chain]. rewrite Int.unsigned_repr by lia.
   unfold V293_tcb_publication_old_tail in B. sep normal in B. sep destruct B.
   (* oldnext is read from the preserved tail cell, not invented. *)
   clear -B Bound OBound. sep auto.
 - cbn[V293_pub_old_head V293_tcb_active_chain]in *.
   unfold V293_tcb_publication_old_tail in B. clear -B Bound;sep auto.
Qed.

Theorem V293_OS_TCBInit_publish_pool_body : forall Spec sd li I r ri tid
 ptcb head group rows counter bc bt base bh bg br bn bo obase (present:bool) k y x g row other next prev R aop ir si cs,
 (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 (0<=obase)%Z -> (obase+55<=Int.max_unsigned)%Z ->
 y<2 -> x<8 -> g<256 -> row<256 -> (if present then S k else O)<255 ->
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_publication_input ptcb head group rows counter bc bt base bh bg br bn y x
 (if present then S k else O)(V293_pub_old_head present bo obase)g row other next prev R aop ir si cs)
 (V293_TCB_publish_body ptcb head group rows counter)
 (V293_tcb_publication_output ptcb head group rows counter bc bt base bh bg br bn y
 (S(if present then S k else O))(Nat.setbit g y)(Nat.setbit row x)other R aop ir si cs)tid.
Proof.
 intros Spec sd li I r ri tid ptcb head group rows counter bc bt base bh bg br bn bo obase present k y x g row other next prev R aop ir si cs Base Bound OBase OBound Y X G Row Count HR.
 eapply conseq_rule;[apply V293_tcb_publication_prepare;assumption|intros s H;exact H| ].
 apply ex_intro_rule. intro oldnext. eapply conseq_rule.
 - intros s H;exact H.
 - apply V293_tcb_publication_finish with(bo:=bo)(obase:=obase)(oldnext:=oldnext);assumption.
 - apply V293_OS_TCBInit_publish_body_hoare;try assumption;try lia.
   unfold V293_tcb_publication_frame. repeat apply V293_star_CurLINV_r. exact HR.
Qed.
Print Assumptions V293_OS_TCBInit_publish_pool_body.

(* The actual initialized node from the preceding Hook path supplies this view;
   no new bytes, address-distinctness premise, or abstract node is introduced. *)
Lemma V293_tcb_publication_initialized_view : forall b off next p top bottom identity size ext options,
 p<13 -> V293_tcb_init_values_valid top bottom identity size ext options ->
 V293_tcb_allocated_initialized b off next p top bottom identity size ext options ==>
 EX prev:val,V293_tcb_publication_new b(Int.unsigned off)(V293_prio_row p)(V293_prio_bit p)next prev.
Proof.
 intros b off next p top bottom identity size ext options Range Valid s H.
 unfold V293_tcb_allocated_initialized,V293_tcb_allocated_remainder,V293_tcb_allocated_spares in H.
 cbn[V293_tcb_init_final_fields V293_rdy_raw_cells V293_storage]in H.
 unfold V293_storage_cell in H. sep normal in H.
 destruct H as(prev&spare40&spare42&spare43&H).
 exists prev. unfold V293_tcb_publication_new,V293_tcb_publication_spare_cells.
 cbn[V293_rdy_raw_cells V293_storage]. unfold V293_storage_cell. sep normal.
 exists top. exists(V293_byteval p). exists(Vint32 Int.zero). exists(Vint32 Int.zero).
 exists(Vint32 Int.zero). exists ext. exists size. exists bottom. exists options. exists identity.
 exists(Vint32 Int.zero). exists(V293_byteval(V293_prio_bit p)).
 exists Vnull. exists Vnull. exists Vnull. exists spare40. exists spare42. exists spare43.
 destruct Valid as(Top&Bottom&Identity&Size&Ext&Options).
 pose proof(V293_byte_type p ltac:(lia))as Prio.
 assert(Bit:V293_prio_bit p<256)by(unfold V293_prio_bit;destruct(p <? 8);lia).
 pose proof(V293_byte_type _ Bit)as BitTyped.
 clear -H Top Bottom Identity Size Ext Options Prio BitTyped;sep auto.
Qed.
