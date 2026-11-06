(* Finite-site refinement of the actual full-byte publication chain.
   Pointer lists are logical indices, not a second copy of heap permissions.
   Establishing this refinement from the production allocator remains open. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEnabledPublication.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublicationPool.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublishHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.basetac.perm_map_lemmas_part1.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Fixpoint V293_tcb_indexed_chain (nodes:list tid) (prev head:val) : asrt :=
 match nodes with
 | [] => [|head=Vnull|]
 | (b,off)::rest =>
   [|head=Vptr(b,off) /\ (Int.unsigned off+55<=Int.max_unsigned)%Z|] **
   (V293_tcb_active_payload b(Int.unsigned off) **
    (EX next:val,[|rule_type_val_match(Tcom_ptr 410%Z)next=true|] **
     (Amapsto(b,(Int.unsigned off+20)%Z)(Tcom_ptr 410%Z)true next **
      (Amapsto(b,(Int.unsigned off+24)%Z)(Tcom_ptr 410%Z)true prev **
       V293_tcb_indexed_chain rest head next))))
 end.

Lemma V293_tcb_indexed_forget : forall nodes prev head,
 V293_tcb_indexed_chain nodes prev head ==>
 V293_tcb_active_chain(length nodes)prev head.
Proof.
 induction nodes as[ |[b off]nodes IH];intros prev head s H;[exact H| ].
 cbn[V293_tcb_indexed_chain]in H. apply astar_l_apure_elim in H.
 destruct H as[[E Bound]H]. subst head. cbn[V293_tcb_active_chain length].
 apply astar_l_apure_intro;[ |exact Bound].
 eapply astar_mono;[intros st HS;exact HS| |exact H].
 intros st[next Hnext]. exists next. apply astar_l_apure_elim in Hnext.
 destruct Hnext as[Typed Hnext]. apply astar_l_apure_intro;[ |exact Typed].
 eapply astar_mono;[intros st1 HS;exact HS| |exact Hnext].
 apply astar_mono;[intros st1 HS;exact HS|apply IH].
Qed.

(* These are the 13 real record starts used by OS_InitTCBList: stride 56.
   No byte ownership is asserted by this pure address catalogue. *)
Definition V293_tcb_table_sites (bt:block) : list tid :=
 map(fun i=>(bt,Int.repr(56*Z.of_nat i))) (seq 0 13).

Lemma V293_tcb_table_sites_length : forall bt,length(V293_tcb_table_sites bt)=13.
Proof. intro bt. unfold V293_tcb_table_sites. rewrite map_length,seq_length. reflexivity. Qed.

Definition V293_tcb_sites_valid (sites nodes:list tid) :=
 NoDup nodes /\ incl nodes sites.

Lemma V293_tcb_sites_count : forall sites nodes,
 V293_tcb_sites_valid sites nodes -> length nodes<=length sites.
Proof. intros sites nodes[ND Included]. eapply NoDup_incl_length;assumption. Qed.

Lemma V293_tcb_table_capacity : forall bt nodes,
 V293_tcb_sites_valid(V293_tcb_table_sites bt)nodes -> length nodes<255.
Proof.
 intros bt nodes H. pose proof(V293_tcb_sites_count _ _ H)as Bound.
 rewrite V293_tcb_table_sites_length in Bound. lia.
Qed.

Lemma V293_tcb_sites_prepend : forall sites nodes node,
 In node sites -> ~In node nodes -> V293_tcb_sites_valid sites nodes ->
 V293_tcb_sites_valid sites(node::nodes).
Proof.
 intros sites nodes node Member Fresh[ND Included]. split.
 - constructor;assumption.
 - intros x[Same|Old];[subst x;exact Member|apply Included;exact Old].
Qed.

Definition V293_tcb_indexed_pool bh bg br bn y nodes head g row other :=
 Amapsto(bh,0%Z)(Tptr V293_tcb_type)true head **
 (Amapsto(bg,0%Z)Tint8 true(V293_byteval g) **
 (Amapsto(br,Z.of_nat y)Tint8 true(V293_byteval row) **
 (Amapsto(br,Z.of_nat(1-y))Tint8 true(V293_byteval other) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval(length nodes)) **
 V293_tcb_indexed_chain nodes Vnull head)))).

Lemma V293_tcb_indexed_pool_forget : forall bh bg br bn y nodes head g row other,
 V293_tcb_indexed_pool bh bg br bn y nodes head g row other ==>
 V293_tcb_publication_pool bh bg br bn y(length nodes)head g row other.
Proof.
 intros bh bg br bn y nodes head g row other.
 unfold V293_tcb_indexed_pool,V293_tcb_publication_pool.
 do 5(eapply astar_mono;[intros s H;exact H| ]). apply V293_tcb_indexed_forget.
Qed.

(* A bound on the CURRENT borrowed chain, not a snapshot retained by a caller. *)
Definition V293_tcb_finite_pool sites bh bg br bn y n head g row other :=
 EX nodes:list tid,[|n=length nodes /\ V293_tcb_sites_valid sites nodes|] **
 V293_tcb_indexed_pool bh bg br bn y nodes head g row other.

Lemma V293_tcb_finite_pool_forget : forall sites bh bg br bn y n head g row other,
 V293_tcb_finite_pool sites bh bg br bn y n head g row other ==>
 V293_tcb_publication_pool bh bg br bn y n head g row other.
Proof.
 intros sites bh bg br bn y n head g row other s[nodes H].
 apply astar_l_apure_elim in H. destruct H as[[E Valid]H]. subst n.
 apply V293_tcb_indexed_pool_forget;exact H.
Qed.

Theorem V293_tcb_finite_pool_capacity : forall bt bh bg br bn y n head g row other s,
 s |= V293_tcb_finite_pool(V293_tcb_table_sites bt)bh bg br bn y n head g row other -> n<255.
Proof.
 intros bt bh bg br bn y n head g row other s[nodes H].
 apply astar_l_apure_elim in H. destruct H as[[E Valid]H]. subst n.
 eapply V293_tcb_table_capacity;exact Valid.
Qed.

Lemma V293_tcb_indexed_member_cell : forall nodes node prev head,
 In node nodes ->
 V293_tcb_indexed_chain nodes prev head ** Atrue ==>
 EX next:val,Amapsto(fst node,(Int.unsigned(snd node)+20)%Z)(Tcom_ptr 410%Z)true next ** Atrue.
Proof.
 induction nodes as[ |[b off]nodes IH];intros node prev head Member s H;[contradiction| ].
 destruct Member as[Same|Member].
 - subst node. cbn[V293_tcb_indexed_chain]in H. sep normal in H. sep destruct H.
   exists x. cbn[fst snd]. clear -H;sep auto.
 - cbn[V293_tcb_indexed_chain]in H. sep normal in H. sep destruct H.
   apply IH with(prev:=head)(head:=x);[exact Member| ]. clear -H;sep auto.
Qed.

Lemma V293_tcb_pointer_first_byte : forall a id v s,
 s |= Amapsto a(Tcom_ptr id)true v ->
 exists byte,get(getmem s)a=Some(true,byte).
Proof.
 intros[b off]id v [[[[[[ge le]M]ir]aux]O]op][[vl[Encode Owned]]Empty].
 assert(L:length vl=4)by(rewrite <-Encode;apply encode_val_length).
 destruct vl as[ |byte bytes];[discriminate| ].
 cbn[ptomvallist]in Owned. destruct Owned as(m1&m2&JM&First&Rest).
 unfold ptomval in First. subst m1. exists byte.
 eapply mem_join_get_get_l_true;[exact JM|apply HalfPermMap.map_get_sig].
Qed.

Lemma V293_tcb_pointer_conflict : forall a id v w,
 Amapsto a(Tcom_ptr id)true v ** Amapsto a(Tcom_ptr id)true w ==> Afalse.
Proof.
 intros a id v w [[[[[[ge le]M]ir]aux]O]op]H.
 apply sat_split in H. destruct H as(m1&m2&o1&o2&JM&JO&H1&H2).
 destruct(V293_tcb_pointer_first_byte _ _ _ _ H1)as[u U].
 destruct(V293_tcb_pointer_first_byte _ _ _ _ H2)as[vv V].
 cbn[getmem get_smem get_mem]in U,V.
 pose proof(@HalfPermMap.map_join_getp_some m1 m2 M a (true,u)(true,vv)(false,u)
 eq_refl JM U V eq_refl)as[_[Impossible _]]. discriminate.
Qed.

Lemma V293_tcb_indexed_private_fresh : forall nodes b off next prev head,
 Amapsto(b,(Int.unsigned off+20)%Z)(Tcom_ptr 410%Z)true next **
 V293_tcb_indexed_chain nodes prev head ** Atrue ==>
 [|~In(b,off)nodes|] **
 (Amapsto(b,(Int.unsigned off+20)%Z)(Tcom_ptr 410%Z)true next **
 V293_tcb_indexed_chain nodes prev head ** Atrue).
Proof.
 intros nodes b off next prev head s H. apply astar_l_apure_intro;[exact H| ].
 intro Member.
 assert(B:s |= Amapsto(b,(Int.unsigned off+20)%Z)(Tcom_ptr 410%Z)true next **
 (V293_tcb_indexed_chain nodes prev head ** Atrue))by(clear -H;sep auto).
 eapply astar_mono in B;[ |intros st HS;exact HS|apply V293_tcb_indexed_member_cell;exact Member].
 sep normal in B. sep destruct B.
 assert(C:s |= (Amapsto(b,(Int.unsigned off+20)%Z)(Tcom_ptr 410%Z)true next **
 Amapsto(b,(Int.unsigned off+20)%Z)(Tcom_ptr 410%Z)true x) ** Atrue)by(clear -B;sep auto).
 eapply astar_mono in C;[ |apply V293_tcb_pointer_conflict|intros st HS;exact HS].
 destruct s as [[[[[[ge le]M]ir]aux]O]op]. apply sat_split in C.
 destruct C as(m1&m2&o1&o2&JM&JO&Impossible&Rest). exact Impossible.
Qed.

Definition V293_tcb_old_sites (present:bool) bo obase tail : list tid :=
 if present then (bo,Int.repr obase)::tail else [].
Definition V293_tcb_indexed_input ptcb head group rows counter bc bt base bh bg br bn y x nodes oldhead g row other next prev R aop ir si cs :=
 <||aop||> ** OS[ir,false,si,cs] **
 V293_pub_bindings ptcb head group rows counter bc bh bg br bn **
 Amapsto(bc,0%Z)(Tptr V293_tcb_type)true(Vptr(bt,Int.repr base)) **
 (V293_tcb_publication_new bt base y x next prev **
 (V293_tcb_indexed_pool bh bg br bn y nodes oldhead g row other ** R)).
Definition V293_tcb_indexed_output ptcb head group rows counter bc bt base bh bg br bn y nodes g row other R aop ir si cs :=
 <||aop||> ** OS[ir,false,si,cs] **
 V293_pub_bindings ptcb head group rows counter bc bh bg br bn **
 Amapsto(bc,0%Z)(Tptr V293_tcb_type)true(Vptr(bt,Int.repr base)) **
 (V293_tcb_indexed_pool bh bg br bn y nodes(Vptr(bt,Int.repr base))g row other ** R).
Definition V293_tcb_indexed_old_tail (present:bool) tail bo obase next :=
 if present then [|rule_type_val_match(Tcom_ptr 410%Z)next=true|] **
 (V293_tcb_active_payload bo obase **
 (Amapsto(bo,(obase+20)%Z)(Tcom_ptr 410%Z)true next **
 V293_tcb_indexed_chain tail(Vptr(bo,Int.repr obase))next)) else Aemp.
Definition V293_tcb_indexed_frame bt base br y other present tail bo obase next R :=
 V293_storage(V293_tcb_publication_spare_cells bt base) **
 (V293_tcb_indexed_old_tail present tail bo obase next **
 (Amapsto(br,Z.of_nat(1-y))Tint8 true(V293_byteval other) ** R)).

Lemma V293_tcb_indexed_prepare : forall ptcb head group rows counter bc bt base bh bg br bn bo obase (present:bool) tail y x g row other next prev R aop ir si cs,
 (0<=obase)%Z -> (obase+55<=Int.max_unsigned)%Z ->
 V293_tcb_indexed_input ptcb head group rows counter bc bt base bh bg br bn y x
 (V293_tcb_old_sites present bo obase tail)(V293_pub_old_head present bo obase)g row other next prev R aop ir si cs ==>
 EX oldnext:val,V293_pub_hstate ptcb head group rows counter bc bh bg br bn
 (V293_pub_cells bc bt base bh bg br bn bo obase present y x next prev
 (V293_pub_old_head present bo obase)g row(length(V293_tcb_old_sites present bo obase tail))Vnull)
 (V293_tcb_indexed_frame bt base br y other present tail bo obase oldnext R)aop ir si cs.
Proof.
 intros ptcb head group rows counter bc bt base bh bg br bn bo obase present tail y x g row other next prev R aop ir si cs Base Bound s H.
 destruct present.
 - unfold V293_tcb_indexed_input,V293_tcb_indexed_pool,V293_pub_old_head in H.
   cbn[V293_tcb_old_sites V293_tcb_indexed_chain]in H.
   rewrite Int.unsigned_repr in H by lia. sep normal in H. sep destruct H.
   exists x0. unfold V293_pub_hstate,V293_tcb_indexed_frame,V293_tcb_indexed_old_tail,
   V293_tcb_publication_new,V293_pub_cells,V293_pub_old_head in *.
   cbn[V293_rdy_raw_cells app]in *;clear -H;sep auto.
 - exists Vnull. unfold V293_tcb_indexed_input,V293_tcb_indexed_pool,V293_tcb_indexed_chain,V293_tcb_old_sites,
   V293_pub_hstate,V293_tcb_indexed_frame,V293_tcb_indexed_old_tail,
   V293_tcb_publication_new,V293_pub_cells,V293_pub_old_head in *.
   cbn[V293_rdy_raw_cells app]in *;clear -H;sep auto.
Qed.

Lemma V293_tcb_indexed_finish : forall ptcb head group rows counter bc bt base bh bg br bn bo obase (present:bool) tail y x g row other oldnext R aop ir si cs,
 (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 (0<=obase)%Z -> (obase+55<=Int.max_unsigned)%Z -> y<2 -> x<8 ->
 V293_pub_hstate ptcb head group rows counter bc bh bg br bn
 (V293_pub_cells bc bt base bh bg br bn bo obase present y x
 (V293_pub_old_head present bo obase)Vnull(Vptr(bt,Int.repr base))
 (Nat.setbit g y)(Nat.setbit row x)(length((bt,Int.repr base)::V293_tcb_old_sites present bo obase tail))(Vptr(bt,Int.repr base)))
 (V293_tcb_indexed_frame bt base br y other present tail bo obase oldnext R)aop ir si cs ==>
 V293_tcb_indexed_output ptcb head group rows counter bc bt base bh bg br bn y
 ((bt,Int.repr base)::V293_tcb_old_sites present bo obase tail)(Nat.setbit g y)(Nat.setbit row x)other R aop ir si cs.
Proof.
 intros ptcb head group rows counter bc bt base bh bg br bn bo obase present tail y x g row other oldnext R aop ir si cs Base Bound OBase OBound Y X s H.
 unfold V293_pub_hstate,V293_pub_cells,V293_tcb_indexed_frame in H.
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
 Amapsto(bn,0%Z)Tint8 true(V293_byteval(length((bt,Int.repr base)::V293_tcb_old_sites present bo obase tail))) **
 ((if present then Amapsto(bo,(obase+24)%Z)(Tcom_ptr 410%Z)true(Vptr(bt,Int.repr base)) else Aemp) **
 V293_tcb_indexed_old_tail present tail bo obase oldnext **
 Amapsto(br,Z.of_nat(1-y))Tint8 true(V293_byteval other) ** R))).
 { destruct present;cbn[V293_rdy_raw_cells]in *;clear -H;sep auto. }
 eapply astar_mono in B;[ |apply V293_tcb_publication_payload_fold;assumption|intros st HS;exact HS].
 unfold V293_tcb_indexed_output,V293_tcb_indexed_pool.
 cbn[V293_tcb_old_sites V293_tcb_indexed_chain]. rewrite Int.unsigned_repr by lia.
 sep normal. exists(V293_pub_old_head present bo obase).
 destruct present.
 - cbn[V293_pub_old_head V293_tcb_old_sites V293_tcb_indexed_chain]. rewrite Int.unsigned_repr by lia.
   unfold V293_tcb_indexed_old_tail in B. sep normal in B. sep destruct B.
   (* oldnext is read from the preserved tail cell, not invented. *)
   clear -B Bound OBound. sep auto.
 - cbn[V293_pub_old_head V293_tcb_old_sites V293_tcb_indexed_chain]in *.
   unfold V293_tcb_indexed_old_tail in B. clear -B Bound;sep auto.
Qed.

(* This is not allocator-token freshness. It follows from the two actual
   full-write Next cells already present in this one borrowed critical state. *)
Lemma V293_tcb_indexed_input_fresh : forall ptcb head group rows counter bc bt base bh bg br bn y x nodes oldhead g row other next prev R aop ir si cs,
 (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 V293_tcb_indexed_input ptcb head group rows counter bc bt base bh bg br bn y x
 nodes oldhead g row other next prev R aop ir si cs ==>
 V293_tcb_indexed_input ptcb head group rows counter bc bt base bh bg br bn y x
 nodes oldhead g row other next prev R aop ir si cs ** [|~In(bt,Int.repr base)nodes|].
Proof.
 intros ptcb head group rows counter bc bt base bh bg br bn y x nodes oldhead g row other next prev R aop ir si cs Base Bound s H.
 assert(B:s |= Amapsto(bt,(Int.unsigned(Int.repr base)+20)%Z)(Tcom_ptr 410%Z)true next **
 V293_tcb_indexed_chain nodes Vnull oldhead ** Atrue).
 { rewrite Int.unsigned_repr by lia.
   unfold V293_tcb_indexed_input,V293_tcb_indexed_pool,V293_tcb_publication_new in H.
   cbn[V293_rdy_raw_cells]in H. clear -H;sep auto. }
 apply V293_tcb_indexed_private_fresh in B. apply astar_l_apure_elim in B.
 destruct B as[Fresh B]. clear -H Fresh;sep auto.
Qed.

Theorem V293_OS_TCBInit_publish_finite_body : forall Spec sd li I r ri tid
 ptcb head group rows counter bc bt base bh bg br bn table bo obase (present:bool) tail y x g row other next prev R aop ir si cs,
 (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 (0<=obase)%Z -> (obase+55<=Int.max_unsigned)%Z ->
 y<2 -> x<8 -> g<256 -> row<256 ->
 V293_tcb_sites_valid(V293_tcb_table_sites table)(V293_tcb_old_sites present bo obase tail) ->
 In(bt,Int.repr base)(V293_tcb_table_sites table) ->
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_indexed_input ptcb head group rows counter bc bt base bh bg br bn y x
 (V293_tcb_old_sites present bo obase tail)(V293_pub_old_head present bo obase)g row other next prev R aop ir si cs)
 (V293_TCB_publish_body ptcb head group rows counter)
 ([|V293_tcb_sites_valid(V293_tcb_table_sites table)
 ((bt,Int.repr base)::V293_tcb_old_sites present bo obase tail)|] **
 V293_tcb_indexed_output ptcb head group rows counter bc bt base bh bg br bn y
 ((bt,Int.repr base)::V293_tcb_old_sites present bo obase tail)
 (Nat.setbit g y)(Nat.setbit row x)other R aop ir si cs)tid.
Proof.
 intros Spec sd li I r ri tid ptcb head group rows counter bc bt base bh bg br bn table bo obase present tail y x g row other next prev R aop ir si cs Base Bound OBase OBound Y X G Row Valid Member HR.
 pose proof(V293_tcb_table_capacity _ _ Valid)as Fits.
 eapply conseq_rule;[apply V293_tcb_indexed_input_fresh;assumption|intros s H;exact H| ].
 apply pure_split_rule. intro Fresh.
 assert(NewValid:V293_tcb_sites_valid(V293_tcb_table_sites table)
 ((bt,Int.repr base)::V293_tcb_old_sites present bo obase tail)).
 { apply V293_tcb_sites_prepend;assumption. }
 eapply conseq_rule;[apply V293_tcb_indexed_prepare;assumption|intros s H;exact H| ].
 apply ex_intro_rule. intro oldnext. eapply conseq_rule.
 - intros s H;exact H.
 - intros s H. apply astar_l_apure_intro;[ |exact NewValid].
   eapply V293_tcb_indexed_finish;try eassumption.
 - apply V293_OS_TCBInit_publish_body_hoare;try assumption;try lia.
   unfold V293_tcb_indexed_frame. repeat apply V293_star_CurLINV_r. exact HR.
Qed.
Print Assumptions V293_OS_TCBInit_publish_finite_body.
