Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublicationPool.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublishHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSecondHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFullPriority.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEnabledHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFreePool.
Require Import CertiOS.certiucos.v293.proofs.V293TCBAllocatedFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReservationOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEnabledPublication.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteSites.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

(* Refined current shared chain; catalogue is pure, bytes are owned once.
   This is an interface to a future production invariant, not that invariant. *)
Definition V293_tcb_finite_shared tcbtable bh bg br bn y :=
 EX present:bool,EX tail:list (block*int32),EX bo:block,EX obase:Z,EX g:nat,EX row:nat,EX other:nat,
 [|(0<=obase)%Z /\ (obase+55<=Int.max_unsigned)%Z /\
   g<256 /\ row<256 /\ other<256 /\
   V293_tcb_sites_valid(V293_tcb_table_sites tcbtable)(V293_tcb_old_sites present bo obase tail)|] **
 V293_tcb_indexed_pool bh bg br bn y(V293_tcb_old_sites present bo obase tail)
   (V293_pub_old_head present bo obase)g row other.

Lemma V293_tcb_finite_shared_forget : forall tcbtable bh bg br bn y,
 V293_tcb_finite_shared tcbtable bh bg br bn y ==>
 V293_tcb_publication_shared bh bg br bn y.
Proof.
 intros tcbtable bh bg br bn y s(present&tail&bo&obase&g&row&other&H).
 apply astar_l_apure_elim in H. destruct H as[[B[Bound[G[Row[Other Valid]]]]]H].
 pose proof(V293_tcb_table_capacity _ _ Valid)as Fits.
 apply V293_tcb_indexed_pool_forget in H.
 unfold V293_tcb_publication_shared. exists present. exists(length tail).
 exists bo. exists obase. exists g. exists row. exists other.
 destruct present;cbn[V293_tcb_old_sites length]in *;apply astar_l_apure_intro;try exact H;repeat split;try assumption;exact(Nat.lt_trans _ 255 256 Fits(Nat.lt_succ_diag_r 255)).
Qed.

Lemma V293_tcb_finite_enter : forall Spec sd li I r ri tid tcbtable ptcb head group rows counter bc bt base bh bg br bn y x next prev K F aop ir si ci,
 (gettopis si<=INUM)%nat -> GoodFrm F ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==>
  Aisr ir ** (V293_tcb_finite_shared tcbtable bh bg br bn y ** K)) ->
 InfRules Spec sd li I r ri
 (V293_tcb_publication_enabled ptcb head group rows counter bc bt base bh bg br bn y x next prev F aop ir si ci)
 (sprim encrit)
 (EX present:bool,EX tail:list (block*int32),EX bo:block,EX obase:Z,EX g:nat,EX row:nat,EX other:nat,
  [|(0<=obase)%Z /\ (obase+55<=Int.max_unsigned)%Z /\
    g<256 /\ row<256 /\ other<256 /\
    V293_tcb_sites_valid(V293_tcb_table_sites tcbtable)(V293_tcb_old_sites present bo obase tail)|] **
  V293_tcb_indexed_input ptcb head group rows counter bc bt base bh bg br bn y x
   (V293_tcb_old_sites present bo obase tail)(V293_pub_old_head present bo obase)g row other next prev(K ** F)aop ir si(true::ci))tid.
Proof.
 intros Spec sd li I r ri tid tcbtable ptcb head group rows counter bc bt base bh bg br bn y x next prev K F aop ir si ci Bound Frame Open.
 unfold V293_tcb_publication_enabled. eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,true,si,ci] ** ATopis(gettopis si) ** [|(gettopis si<=INUM)%nat|] **
 V293_tcb_publication_private ptcb head group rows counter bc bt base bh bg br bn y x next prev F)
 (q:=<||aop||> ** OS[ir,false,si,true::ci] ** invlth_isr I 0(gettopis si) **
 V293_tcb_publication_private ptcb head group rows counter bc bt base bh bg br bn y x next prev F).
 - intros s H. assert(S:s |= Ais si ** Atrue)by(clear -H;sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top. apply astar_l_atopis_elim in Top.
   destruct Top as[Top _]. pose proof(@astar_l_atopis_intro s(gettopis si)_ H Top)as HT.
   clear -HT Bound;sep auto.
 - intros s H.
   assert(B:s |= (Aisr ir ** invlth_isr I 0(gettopis si)) **
   (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) **
   V293_tcb_publication_private ptcb head group rows counter bc bt base bh bg br bn y x next prev F))by(clear -H;sep auto).
   eapply astar_mono in B;[ |exact Open|intros st HS;exact HS].
   unfold V293_tcb_finite_shared in B. sep normal in B. sep destruct B.
   unfold V293_tcb_indexed_input,V293_tcb_publication_private in *.
   clear -B;sep auto.
 - apply encrit1_rule. apply V293_tcb_publication_private_good;exact Frame.
Qed.

Lemma V293_tcb_finite_exit : forall Spec sd li I r ri tid tcbtable ptcb head group rows counter bc bt base bh bg br bn y nodes g row other K F aop ir si ci,
 (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z -> g<256 -> row<256 -> other<256 ->
 GoodFrm F -> (F ==> CurLINV li tid) ->
 (Aisr ir ** (V293_tcb_finite_shared tcbtable bh bg br bn y ** K) ==>
  Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 ([|V293_tcb_sites_valid(V293_tcb_table_sites tcbtable)((bt,Int.repr base)::nodes)|] **
 V293_tcb_indexed_output ptcb head group rows counter bc bt base bh bg br bn y
 ((bt,Int.repr base)::nodes)g row other(K ** F)aop ir si(true::ci))
 (sprim excrit)
 (V293_tcb_publication_returned ptcb head group rows counter bc bt base bh bg br bn F aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid tcbtable ptcb head group rows counter bc bt base bh bg br bn y nodes g row other K F aop ir si ci Base Bound G Row Other Frame HR Close.
 eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis(gettopis si) ** invlth_isr I 0(gettopis si) **
 (V293_pub_bindings ptcb head group rows counter bc bh bg br bn **
 (Amapsto(bc,0%Z)(Tptr V293_tcb_type)true(Vptr(bt,Int.repr base)) ** F)))
 (q:=<||aop||> ** OS[ir,true,si,ci] **
 (V293_pub_bindings ptcb head group rows counter bc bh bg br bn **
 (Amapsto(bc,0%Z)(Tptr V293_tcb_type)true(Vptr(bt,Int.repr base)) ** F))).
 - intros s H. apply astar_l_apure_elim in H. destruct H as[Valid H].
   assert(P:s |= (Aisr ir ** (V293_tcb_finite_shared tcbtable bh bg br bn y ** K)) **
   (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) **
   (V293_pub_bindings ptcb head group rows counter bc bh bg br bn **
   (Amapsto(bc,0%Z)(Tptr V293_tcb_type)true(Vptr(bt,Int.repr base)) ** F)))).
   { unfold V293_tcb_finite_shared. sep normal.
     exists true. exists nodes. exists bt. exists base. exists g. exists row. exists other.
     unfold V293_tcb_indexed_output,V293_pub_old_head,V293_tcb_old_sites in *.
     clear -H Base Bound G Row Other Valid;sep auto. tauto. }
   eapply astar_mono in P;[ |exact Close|intros st HS;exact HS].
   assert(S:s |= Ais si ** Atrue)by(clear -P;sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top. apply astar_l_atopis_elim in Top.
   destruct Top as[Top _]. pose proof(@astar_l_atopis_intro s(gettopis si)_ P Top)as HT.
   clear -HT;sep auto.
 - unfold V293_tcb_publication_returned. intros s H;clear -H;sep auto.
 - apply excrit1_rule.
   + cbn[V293_pub_bindings GoodFrm];tauto.
   + repeat apply V293_star_CurLINV_r;exact HR.
Qed.

(* Whole original enabled suffix: no independent Capacity premise.
   Member still needs an allocator preservation proof. *)
Theorem V293_OS_TCBInit_publish_finite_enabled : forall Spec sd li I r tid tcbtable
 ptcb head group rows counter bc bt base bh bg br bn y x next prev K F aop ir si ci,
 (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z -> y<2 -> x<8 ->
 In(bt,Int.repr base)(V293_tcb_table_sites tcbtable) ->
 (gettopis si<=INUM)%nat -> GoodFrm F -> (F ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** (V293_tcb_finite_shared tcbtable bh bg br bn y ** K)) ->
 (Aisr ir ** (V293_tcb_finite_shared tcbtable bh bg br bn y ** K) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 (V293_tcb_publication_returned ptcb head group rows counter bc bt base bh bg br bn F aop ir si ci ==> r(Some(Vint32 Int.zero))) ->
 InfRules Spec sd li I r Afalse
 (V293_tcb_publication_enabled ptcb head group rows counter bc bt base bh bg br bn y x next prev F aop ir si ci)
 (V293_TCB_publish ptcb head group rows counter)Afalse tid.
Proof.
 intros Spec sd li I r tid tcbtable ptcb head group rows counter bc bt base bh bg br bn y x next prev K F aop ir si ci Base Bound Y X Member Top Frame HR Open Close Return.
 unfold V293_TCB_publish. eapply seq_rule.
 - apply V293_tcb_finite_enter with(tcbtable:=tcbtable)(K:=K);assumption.
 - apply ex_intro_rule. intro present. apply ex_intro_rule. intro tail.
   apply ex_intro_rule. intro bo. apply ex_intro_rule. intro obase.
   apply ex_intro_rule. intro g. apply ex_intro_rule. intro row.
   apply ex_intro_rule. intro other.
   eapply conseq_rule with(p:=
    V293_tcb_indexed_input ptcb head group rows counter bc bt base bh bg br bn y x
     (V293_tcb_old_sites present bo obase tail)(V293_pub_old_head present bo obase)g row other next prev(K ** F)aop ir si(true::ci) **
    [|(0<=obase)%Z /\ (obase+55<=Int.max_unsigned)%Z /\
       g<256 /\ row<256 /\ other<256 /\
       V293_tcb_sites_valid(V293_tcb_table_sites tcbtable)(V293_tcb_old_sites present bo obase tail)|]).
   + intros s H;clear -H;sep auto.
   + intros s H;exact H.
   + apply pure_split_rule. intros [old_base [old_bound [group_range [row_range [other_range Valid]]]]].
     eapply seq_rule.
     * apply V293_OS_TCBInit_publish_finite_body with(table:=tcbtable);try assumption.
       apply V293_star_CurLINV_r;exact HR.
     * eapply seq_rule.
       -- apply V293_tcb_finite_exit with(tcbtable:=tcbtable)(y:=y)
          (nodes:=V293_tcb_old_sites present bo obase tail)
          (g:=Nat.setbit g y)(row:=Nat.setbit row x)(other:=other)(K:=K);try assumption.
          ++ exact(proj1(proj2(V293_rekey_byte_arithmetic g y group_range ltac:(lia)))).
          ++ exact(proj1(proj2(V293_rekey_byte_arithmetic row x row_range X))).
       -- apply rete_rule with(v:=Vint32 Int.zero)(t:=Tint32).
          intros s H. split;[apply Return;exact H| ].
          destruct s as [[[[[[ge le] M] irq] aux] O] op].
          cbn[sat evalval evaltype getsmem get_smem]. repeat split;try reflexivity;discriminate.
Qed.
Print Assumptions V293_OS_TCBInit_publish_finite_enabled.

(* Original full body, conditional on actual allocator membership, token
   freshness, same-invariant borrowing and Hook contracts; no Capacity. *)
Theorem V293_OS_TCBInit_free_body_finite_published : forall Spec sd li I r tid hi hc tcbtable
 table reserved bf bp bc pc cpu Kfree Kprio Kpub bh bg br bn bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci
 (good:GoodFunAsrt(V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))),
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm R ->
 V293_tcb_init_values_valid top bottom identity size ext options -> (R ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** (V293_tcb_free_pool bf ** Kfree)) ->
 (Aisr ir ** (V293_tcb_free_pool bf ** Kfree) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** V293_create_owned_pool table reserved p Kprio) ->
 (Aisr ir ** V293_create_owned_pool table reserved p Kprio ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 Spec hi=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))aop ir si ci tid good,
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))aop ir si ci tid good,(Tvoid,[Tptr V293_tcb_type])) ->
 Spec hc=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options (V293_tcb_publication_globals bh bg br bn ** R) aop ir si ci tid (proj2 good),
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options (V293_tcb_publication_globals bh bg br bn ** R) aop ir si ci tid (proj2 good),(Tvoid,[Tptr V293_tcb_type])) ->
 (V293_tcb_enabled_state bf bp bc Vnull(Vint32 Int.zero)
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))))aop ir si ci ==>
 r(Some(Vint32(Int.repr 66)))) ->
 (forall b off next s,
 s |= V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))))aop ir si ci ->
 (b,off)<>reserved) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==>
 Aisr ir ** (V293_tcb_finite_shared tcbtable bh bg br bn(V293_prio_row p) ** Kpub)) ->
 (Aisr ir ** (V293_tcb_finite_shared tcbtable bh bg br bn(V293_prio_row p) ** Kpub) ==>
 Aisr ir ** invlth_isr I 0(gettopis si)) ->
 (forall b off next s,
 s |= V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_tcb_publication_globals bh bg br bn ** R)))aop ir si ci ->
 In(b,off)(V293_tcb_table_sites tcbtable)) ->
 (forall b off,
 V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_tcb_publication_globals bh bg br bn ** R)))aop ir si ci ==>
 r(Some(Vint32 Int.zero))) ->
 InfRules Spec sd li I r Afalse
 (V293_tcb_enabled_state bf bp bc pc cpu
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))))aop ir si ci)
 (V293_TCBInit_function_body hi hc)Afalse tid.
Proof.
 intros Spec sd li I r tid hi hc tcbtable table reserved bf bp bc pc cpu Kfree Kprio Kpub bh bg br bn bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci good Range Bound Frame Valid HR FreeOpen FreeClose PriorityOpen PriorityClose FirstLookup SecondLookup Empty Fresh PubOpen PubClose Member Return.
 apply V293_OS_TCBInit_free_body_after_second_hook with(reserved:=reserved)(Kfree:=Kfree)(Kprio:=Kprio)(good:=good);try assumption.
 - cbn[V293_tcb_publication_globals GoodFrm];tauto.
 - apply V293_star_CurLINV_r;exact HR.
 - intros b off next NodeBound NextTyped.
   eapply conseq_rule with(p:=V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_tcb_publication_globals bh bg br bn ** R)))aop ir si ci **
   [|In(b,off)(V293_tcb_table_sites tcbtable)|]).
   + intros s H. pose proof(Member b off next s H)as NodeMember. clear -H NodeMember;sep auto.
   + intros s H;exact H.
   + apply pure_split_rule. intro NodeMember. eapply conseq_rule.
     * apply V293_tcb_full_publication_view;assumption.
     * intros s H;exact H.
     * apply ex_intro_rule. intro prev.
     apply V293_OS_TCBInit_publish_finite_enabled with(tcbtable:=tcbtable)(K:=Kpub);try assumption.
       -- pose proof(Int.unsigned_range off);lia.
       -- unfold V293_prio_row. destruct(p <? 8);lia.
       -- unfold V293_prio_bit. destruct(p <? 8)eqn:E;apply Nat.ltb_lt in E||apply Nat.ltb_ge in E;lia.
       -- rewrite Int.repr_unsigned. exact NodeMember.
       -- apply V293_tcb_publication_caller_frame_good;exact Frame.
       -- apply V293_tcb_publication_caller_frame_linv;exact HR.
       -- intros s H. apply Return with(b:=b)(off:=off). eapply V293_tcb_full_publication_restore;exact H.
Qed.
Print Assumptions V293_OS_TCBInit_free_body_finite_published.
