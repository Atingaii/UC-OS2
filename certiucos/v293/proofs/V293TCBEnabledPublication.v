(* Enabled publication borrows current shared bytes from the same invariant.
   Capacity, production open/close, freshness and Hook bodies remain explicit. *)
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
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

(* The witnesses are chosen by the shared heap, never by the enabled caller.
   Count255 may be stored, but insertion requires a separate capacity proof. *)
Definition V293_tcb_publication_shared bh bg br bn y :=
 EX present:bool,EX k:nat,EX bo:block,EX obase:Z,EX g:nat,EX row:nat,EX other:nat,
 [|(0<=obase)%Z /\ (obase+55<=Int.max_unsigned)%Z /\
   g<256 /\ row<256 /\ other<256 /\ (if present then S k else O)<256|] **
 V293_tcb_publication_pool bh bg br bn y(if present then S k else O)
   (V293_pub_old_head present bo obase)g row other.
Definition V293_tcb_publication_private ptcb head group rows counter bc bt base bh bg br bn y x next prev F :=
 V293_pub_bindings ptcb head group rows counter bc bh bg br bn **
 (Amapsto(bc,0%Z)(Tptr V293_tcb_type)true(Vptr(bt,Int.repr base)) **
 (V293_tcb_publication_new bt base y x next prev ** F)).
Definition V293_tcb_publication_enabled ptcb head group rows counter bc bt base bh bg br bn y x next prev F aop ir si ci :=
 <||aop||> ** OS[ir,true,si,ci] **
 V293_tcb_publication_private ptcb head group rows counter bc bt base bh bg br bn y x next prev F.
Definition V293_tcb_publication_returned ptcb head group rows counter bc bt base bh bg br bn F aop ir si ci :=
 <||aop||> ** OS[ir,true,si,ci] ** V293_pub_bindings ptcb head group rows counter bc bh bg br bn **
 Amapsto(bc,0%Z)(Tptr V293_tcb_type)true(Vptr(bt,Int.repr base)) ** F.
Lemma V293_tcb_publication_private_good : forall ptcb head group rows counter bc bt base bh bg br bn y x next prev F,
 GoodFrm F -> GoodFrm(V293_tcb_publication_private ptcb head group rows counter bc bt base bh bg br bn y x next prev F).
Proof.
 intros. cbn[V293_tcb_publication_private V293_pub_bindings V293_tcb_publication_new
 V293_rdy_raw_cells GoodFrm]. repeat split;try exact I;try assumption.
Qed.

Lemma V293_tcb_publication_enter : forall Spec sd li I r ri tid ptcb head group rows counter bc bt base bh bg br bn y x next prev K F aop ir si ci,
 (gettopis si<=INUM)%nat -> GoodFrm F ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==>
  Aisr ir ** (V293_tcb_publication_shared bh bg br bn y ** K)) ->
 InfRules Spec sd li I r ri
 (V293_tcb_publication_enabled ptcb head group rows counter bc bt base bh bg br bn y x next prev F aop ir si ci)
 (sprim encrit)
 (EX present:bool,EX k:nat,EX bo:block,EX obase:Z,EX g:nat,EX row:nat,EX other:nat,
  [|(0<=obase)%Z /\ (obase+55<=Int.max_unsigned)%Z /\
    g<256 /\ row<256 /\ other<256 /\ (if present then S k else O)<256|] **
  V293_tcb_publication_input ptcb head group rows counter bc bt base bh bg br bn y x
   (if present then S k else O)(V293_pub_old_head present bo obase)g row other next prev(K ** F)aop ir si(true::ci))tid.
Proof.
 intros Spec sd li I r ri tid ptcb head group rows counter bc bt base bh bg br bn y x next prev K F aop ir si ci Bound Frame Open.
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
   unfold V293_tcb_publication_shared in B. sep normal in B. sep destruct B.
   unfold V293_tcb_publication_input,V293_tcb_publication_private in *.
   clear -B;sep auto.
 - apply encrit1_rule. apply V293_tcb_publication_private_good;exact Frame.
Qed.

Lemma V293_tcb_publication_exit : forall Spec sd li I r ri tid ptcb head group rows counter bc bt base bh bg br bn y n g row other K F aop ir si ci,
 (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z -> n<256 -> g<256 -> row<256 -> other<256 ->
 GoodFrm F -> (F ==> CurLINV li tid) ->
 (Aisr ir ** (V293_tcb_publication_shared bh bg br bn y ** K) ==>
  Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_tcb_publication_output ptcb head group rows counter bc bt base bh bg br bn y n g row other(K ** F)aop ir si(true::ci))
 (sprim excrit)
 (V293_tcb_publication_returned ptcb head group rows counter bc bt base bh bg br bn F aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid ptcb head group rows counter bc bt base bh bg br bn y n g row other K F aop ir si ci Base Bound Count G Row Other Frame HR Close.
 eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis(gettopis si) ** invlth_isr I 0(gettopis si) **
 (V293_pub_bindings ptcb head group rows counter bc bh bg br bn **
 (Amapsto(bc,0%Z)(Tptr V293_tcb_type)true(Vptr(bt,Int.repr base)) ** F)))
 (q:=<||aop||> ** OS[ir,true,si,ci] **
 (V293_pub_bindings ptcb head group rows counter bc bh bg br bn **
 (Amapsto(bc,0%Z)(Tptr V293_tcb_type)true(Vptr(bt,Int.repr base)) ** F))).
 - intros s H.
   assert(P:s |= (Aisr ir ** (V293_tcb_publication_shared bh bg br bn y ** K)) **
   (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) **
   (V293_pub_bindings ptcb head group rows counter bc bh bg br bn **
   (Amapsto(bc,0%Z)(Tptr V293_tcb_type)true(Vptr(bt,Int.repr base)) ** F)))).
   { destruct n as[ |k].
     - (* A newly published chain cannot have zero nodes. *)
       unfold V293_tcb_publication_output,V293_tcb_publication_pool in H.
       cbn[V293_tcb_active_chain]in H. sep normal in H. sep destruct H. sep split in H. discriminate.
     - unfold V293_tcb_publication_shared. sep normal.
       exists true. exists k. exists bt. exists base. exists g. exists row. exists other.
       unfold V293_tcb_publication_output,V293_pub_old_head in *.
       clear -H Base Bound Count G Row Other;sep auto. tauto. }
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

Theorem V293_OS_TCBInit_publish_enabled : forall Spec sd li I r tid
 ptcb head group rows counter bc bt base bh bg br bn y x next prev K F aop ir si ci,
 (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z -> y<2 -> x<8 ->
 (gettopis si<=INUM)%nat -> GoodFrm F -> (F ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** (V293_tcb_publication_shared bh bg br bn y ** K)) ->
 (Aisr ir ** (V293_tcb_publication_shared bh bg br bn y ** K) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 (forall (present:bool) k bo obase g row other s,
  s |= V293_tcb_publication_input ptcb head group rows counter bc bt base bh bg br bn y x
   (if present then S k else O)(V293_pub_old_head present bo obase)g row other next prev(K ** F)aop ir si(true::ci) ->
  (if present then S k else O)<255) ->
 (V293_tcb_publication_returned ptcb head group rows counter bc bt base bh bg br bn F aop ir si ci ==> r(Some(Vint32 Int.zero))) ->
 InfRules Spec sd li I r Afalse
 (V293_tcb_publication_enabled ptcb head group rows counter bc bt base bh bg br bn y x next prev F aop ir si ci)
 (V293_TCB_publish ptcb head group rows counter)Afalse tid.
Proof.
 intros Spec sd li I r tid ptcb head group rows counter bc bt base bh bg br bn y x next prev K F aop ir si ci Base Bound Y X Top Frame HR Open Close Capacity Return.
 unfold V293_TCB_publish. eapply seq_rule.
 - apply V293_tcb_publication_enter with(K:=K);assumption.
 - apply ex_intro_rule. intro present. apply ex_intro_rule. intro k.
   apply ex_intro_rule. intro bo. apply ex_intro_rule. intro obase.
   apply ex_intro_rule. intro g. apply ex_intro_rule. intro row.
   apply ex_intro_rule. intro other.
   eapply conseq_rule with(p:=
    V293_tcb_publication_input ptcb head group rows counter bc bt base bh bg br bn y x
     (if present then S k else O)(V293_pub_old_head present bo obase)g row other next prev(K ** F)aop ir si(true::ci) **
    [|(0<=obase)%Z /\ (obase+55<=Int.max_unsigned)%Z /\
       g<256 /\ row<256 /\ other<256 /\ (if present then S k else O)<256|]).
   + intros s H;clear -H;sep auto.
   + intros s H;exact H.
   + apply pure_split_rule. intros [old_base [old_bound [group_range [row_range [other_range count_range]]]]].
     eapply conseq_rule with(p:=
      V293_tcb_publication_input ptcb head group rows counter bc bt base bh bg br bn y x
       (if present then S k else O)(V293_pub_old_head present bo obase)g row other next prev(K ** F)aop ir si(true::ci) **
      [|(if present then S k else O)<255|]).
     * intros s H. pose proof(Capacity present k bo obase g row other s H)as Fits.
       clear -H Fits;sep auto.
     * intros s H;exact H.
     * apply pure_split_rule. intro Fits. eapply seq_rule.
       -- apply V293_OS_TCBInit_publish_pool_body;try assumption.
          apply V293_star_CurLINV_r;exact HR.
       -- eapply seq_rule.
          ++ apply V293_tcb_publication_exit with(y:=y)(n:=S(if present then S k else O))
          (g:=Nat.setbit g y)(row:=Nat.setbit row x)(other:=other)(K:=K);try assumption;try lia.
             ** exact(proj1(proj2(V293_rekey_byte_arithmetic g y group_range ltac:(lia)))).
             ** exact(proj1(proj2(V293_rekey_byte_arithmetic row x row_range X))).
          ++ apply rete_rule with(v:=Vint32 Int.zero)(t:=Tint32).
          intros s H. split;[apply Return;exact H| ].
          destruct s as [[[[[[ge le] M] irq] aux] O] op].
          cbn[sat evalval evaltype getsmem get_smem]. repeat split;try reflexivity;discriminate.
Qed.

Print Assumptions V293_OS_TCBInit_publish_enabled.

(* Environment bindings only: no shared head, bitmap or count byte. *)
Definition V293_tcb_publication_globals bh bg br bn :=
 A_notin_lenv 93%Z //\\ Agvarenv 93%Z(Tptr V293_tcb_type)(bh,0%Z) //\\
 A_notin_lenv 94%Z //\\ Agvarenv 94%Z Tint8(bg,0%Z) //\\
 A_notin_lenv 95%Z //\\ Agvarenv 95%Z(Tarray Tint8 2)(br,0%Z) //\\
 A_notin_lenv 96%Z //\\ Agvarenv 96%Z Tint8(bn,0%Z).
Definition V293_tcb_publication_caller_frame table bf bp bc bprio bs bb bi bz be bo
 p top bottom identity size ext options R :=
 V293_tcb_empty_bindings bf bp bc ** Amapsto(bc,0%Z)Tint32 true(Vint32 Int.zero) **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** R).
Lemma V293_tcb_publication_caller_frame_good : forall table bf bp bc bprio bs bb bi bz be bo
 p top bottom identity size ext options R,
 GoodFrm R -> GoodFrm(V293_tcb_publication_caller_frame table bf bp bc bprio bs bb bi bz be bo
 p top bottom identity size ext options R).
Proof.
 intros. cbn[V293_tcb_publication_caller_frame V293_tcb_empty_bindings V293_tcb_allocated_inputs
 V293_rdy_raw_cells V293_tcb_fields_bindings V293_tcb_table_binding GoodFrm]. tauto.
Qed.
Lemma V293_tcb_publication_caller_frame_linv : forall table bf bp bc bprio bs bb bi bz be bo
 p top bottom identity size ext options R li tid,
 (R ==> CurLINV li tid) ->
 V293_tcb_publication_caller_frame table bf bp bc bprio bs bb bi bz be bo
 p top bottom identity size ext options R ==> CurLINV li tid.
Proof.
 intros table bf bp bc bprio bs bb bi bz be bo p top bottom identity size ext options R li tid HR.
 unfold V293_tcb_publication_caller_frame,V293_tcb_allocated_inputs.
 cbn[V293_rdy_raw_cells]. repeat apply V293_star_CurLINV_r. exact HR.
Qed.
Lemma V293_tcb_empty_ptcb_copy : forall bf bp bc,
 V293_tcb_empty_bindings bf bp bc ==>
 Alvarenv 108%Z(Tptr V293_tcb_type)(bp,0%Z) ** V293_tcb_empty_bindings bf bp bc.
Proof.
 intros bf bp bc s H. destruct s as [[[[[[ge le] M] irq] aux] O] op].
 apply sat_split'. exists empmem. exists M. exists empabst. exists O.
 split;[apply map_join_comm;apply map_join_emp| ].
 split;[apply map_join_comm;apply map_join_emp| ]. split;[ |exact H].
 unfold V293_tcb_empty_bindings in H. destruct H as[HP Rest].
 destruct HP as[b[E[B[HM HO]]]]. cbn[sat]in *;exists b;repeat split;try assumption;reflexivity.
Qed.
Lemma V293_tcb_publication_bindings_split : forall bp bh bg br bn,
 V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z bp bh bg br bn ==>
 Alvarenv 108%Z(Tptr V293_tcb_type)(bp,0%Z) ** V293_tcb_publication_globals bh bg br bn.
Proof.
 intros bp bh bg br bn s H. destruct s as [[[[[[ge le] M] irq] aux] O] op].
 unfold V293_pub_bindings in H. destruct H as[HP HG].
 destruct HP as[b[E[B[HM HO]]]]. cbn[getmem getabst get_smem get_mem]in HM,HO.
 subst M. unfold emposabst in HO;subst O.
 apply sat_split'. exists empmem. exists empmem. exists empabst. exists empabst.
 split;[apply map_join_emp| ]. split;[apply map_join_emp| ].
 split;[exists b;repeat split;try assumption;reflexivity|exact HG].
Qed.
Lemma V293_tcb_publication_bindings_join : forall bp bh bg br bn,
 Alvarenv 108%Z(Tptr V293_tcb_type)(bp,0%Z) ** V293_tcb_publication_globals bh bg br bn ==>
 V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z bp bh bg br bn.
Proof.
 intros bp bh bg br bn s H. destruct s as [[[[[[ge le] M] irq] aux] O] op].
 apply sat_split in H. destruct H as[m1[m2[o1[o2[JM[JO[HP HG]]]]]]].
 destruct HP as[b[E[B[HM HO]]]]. cbn[getmem getabst get_smem get_mem]in HM,HO.
 subst m1. unfold emposabst in HO;subst o1.
 apply map_join_emp'' in JM,JO. subst.
 assert(Empty:empst(ge,le,M,irq,aux,O,op))by exact(proj2(proj1 HG)).
 destruct Empty as[HM HO]. cbn in HM,HO. unfold emposabst in HO. subst M O. unfold V293_pub_bindings.
 split;[exists b;repeat split;try assumption;reflexivity|exact HG].
Qed.
Lemma V293_tcb_empty_ptcb_drop : forall bf bp bc,
 Alvarenv 108%Z(Tptr V293_tcb_type)(bp,0%Z) ** V293_tcb_empty_bindings bf bp bc ==>
 V293_tcb_empty_bindings bf bp bc.
Proof.
 intros bf bp bc s H. destruct s as [[[[[[ge le] M] irq] aux] O] op].
 apply sat_split in H. destruct H as[m1[m2[o1[o2[JM[JO[HP H]]]]]]].
 destruct HP as[b[E[B[HM HO]]]]. cbn[getmem getabst get_smem get_mem]in HM,HO.
 subst m1. unfold emposabst in HO;subst o1.
 apply map_join_emp'' in JM,JO. subst. exact H.
Qed.
Lemma V293_tcb_full_publication_view : forall table bf bp bc b off next bh bg br bn
 bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci,
 p<13 -> V293_tcb_init_values_valid top bottom identity size ext options ->
 V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_tcb_publication_globals bh bg br bn ** R)))aop ir si ci ==>
 EX prev:val,V293_tcb_publication_enabled 108%Z 93%Z 94%Z 95%Z 96%Z bp b(Int.unsigned off)
 bh bg br bn(V293_prio_row p)(V293_prio_bit p)next prev
 (V293_tcb_publication_caller_frame table bf bp bc bprio bs bb bi bz be bo
 p top bottom identity size ext options R)aop ir si ci.
Proof.
 intros table bf bp bc b off next bh bg br bn bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci Range Valid s H.
 unfold V293_tcb_enabled_state,V293_tcb_enabled_resources in H.
 eapply astar_mono in H;[ |intros st HS;exact HS| ].
 2:{ eapply astar_mono;[intros st HS;exact HS| ].
     eapply astar_mono;[intros st HS;exact HS| ].
     eapply astar_mono;[intros st HS;exact HS| ].
     eapply astar_mono;[intros st HS;exact HS| ].
     eapply astar_mono;[apply V293_tcb_publication_initialized_view;assumption|intros st HS;exact HS]. }
 sep normal in H. sep destruct H.
 unfold V293_tcb_allocated_inputs in H. cbn[V293_rdy_raw_cells]in H.
 (* Copy the empty-memory environment fact while retaining all actual bytes. *)
 assert(C:s |= V293_tcb_empty_bindings bf bp bc **
 (<||aop||> ** OS[ir,true,si,ci] ** Amapsto(bp,0%Z)(Tptr V293_tcb_type)true(Vptr(b,off)) **
 Amapsto(bc,0%Z)Tint32 true(Vint32 Int.zero) **
 V293_tcb_publication_new b(Int.unsigned off)(V293_prio_row p)(V293_prio_bit p)next x **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_tcb_publication_globals bh bg br bn ** R)))).
 { unfold V293_tcb_allocated_inputs;cbn[V293_rdy_raw_cells];clear -H;sep auto. }
 eapply astar_mono in C;[ |apply V293_tcb_empty_ptcb_copy|intros st HS;exact HS].
 assert(D:s |= (Alvarenv 108%Z(Tptr V293_tcb_type)(bp,0%Z) ** V293_tcb_publication_globals bh bg br bn) **
 (Amapsto(bp,0%Z)(Tptr V293_tcb_type)true(Vptr(b,off)) **
 V293_tcb_publication_new b(Int.unsigned off)(V293_prio_row p)(V293_prio_bit p)next x **
 V293_tcb_publication_caller_frame table bf bp bc bprio bs bb bi bz be bo p top bottom identity size ext options R **
 <||aop||> ** OS[ir,true,si,ci])).
 { unfold V293_tcb_publication_caller_frame,V293_tcb_allocated_inputs in *.
   cbn[V293_rdy_raw_cells]in *;clear -C;sep auto. }
 eapply astar_mono in D;[ |apply V293_tcb_publication_bindings_join|intros st HS;exact HS].
 exists x. unfold V293_tcb_publication_enabled,V293_tcb_publication_private.
 rewrite Int.repr_unsigned. clear -D;sep auto.
Qed.

Lemma V293_tcb_full_publication_restore : forall table bf bp bc b off bh bg br bn
 bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci,
 V293_tcb_publication_returned 108%Z 93%Z 94%Z 95%Z 96%Z bp b(Int.unsigned off)bh bg br bn
 (V293_tcb_publication_caller_frame table bf bp bc bprio bs bb bi bz be bo
 p top bottom identity size ext options R)aop ir si ci ==>
 V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_tcb_publication_globals bh bg br bn ** R)))aop ir si ci.
Proof.
 intros table bf bp bc b off bh bg br bn bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci s H.
 unfold V293_tcb_publication_returned in H. rewrite Int.repr_unsigned in H.
 assert(B:s |= V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z bp bh bg br bn **
 (Amapsto(bp,0%Z)(Tptr V293_tcb_type)true(Vptr(b,off)) **
 V293_tcb_publication_caller_frame table bf bp bc bprio bs bb bi bz be bo
 p top bottom identity size ext options R ** <||aop||> ** OS[ir,true,si,ci])).
 { clear -H;sep auto. }
 eapply astar_mono in B;[ |apply V293_tcb_publication_bindings_split|intros st HS;exact HS].
 assert(C:s |= (Alvarenv 108%Z(Tptr V293_tcb_type)(bp,0%Z) ** V293_tcb_empty_bindings bf bp bc) **
 (V293_tcb_publication_globals bh bg br bn ** Amapsto(bp,0%Z)(Tptr V293_tcb_type)true(Vptr(b,off)) **
 Amapsto(bc,0%Z)Tint32 true(Vint32 Int.zero) **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** R) ** <||aop||> ** OS[ir,true,si,ci])).
 { unfold V293_tcb_publication_caller_frame in B;clear -B;sep auto. }
 eapply astar_mono in C;[ |apply V293_tcb_empty_ptcb_drop|intros st HS;exact HS].
 unfold V293_tcb_enabled_state,V293_tcb_enabled_resources,V293_tcb_allocated_inputs in *.
 cbn[V293_rdy_raw_cells]in *;clear -C;sep auto.
Qed.

(* Original full body: no unproved Hoare continuation. This remains conditional
   on physical pool interfaces, capacity, allocator freshness and Hook contracts. *)
Theorem V293_OS_TCBInit_free_body_published : forall Spec sd li I r tid hi hc
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
 Aisr ir ** (V293_tcb_publication_shared bh bg br bn(V293_prio_row p) ** Kpub)) ->
 (Aisr ir ** (V293_tcb_publication_shared bh bg br bn(V293_prio_row p) ** Kpub) ==>
 Aisr ir ** invlth_isr I 0(gettopis si)) ->
 (forall b off next prev (present:bool) k oldb oldbase g row other s,
 s |= V293_tcb_publication_input 108%Z 93%Z 94%Z 95%Z 96%Z bp b(Int.unsigned off)
 bh bg br bn(V293_prio_row p)(V293_prio_bit p)
 (if present then S k else O)(V293_pub_old_head present oldb oldbase)g row other next prev
 (Kpub ** V293_tcb_publication_caller_frame table bf bp bc bprio bs bb bi bz be bo
 p top bottom identity size ext options R)aop ir si(true::ci) ->
 (if present then S k else O)<255) ->
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
 intros Spec sd li I r tid hi hc table reserved bf bp bc pc cpu Kfree Kprio Kpub bh bg br bn bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci good Range Bound Frame Valid HR FreeOpen FreeClose PriorityOpen PriorityClose FirstLookup SecondLookup Empty Fresh PubOpen PubClose Capacity Return.
 apply V293_OS_TCBInit_free_body_after_second_hook with(reserved:=reserved)(Kfree:=Kfree)(Kprio:=Kprio)(good:=good);try assumption.
 - cbn[V293_tcb_publication_globals GoodFrm];tauto.
 - apply V293_star_CurLINV_r;exact HR.
 - intros b off next NodeBound NextTyped.
   eapply conseq_rule.
   + apply V293_tcb_full_publication_view;assumption.
   + intros s H;exact H.
   + apply ex_intro_rule. intro prev.
     apply V293_OS_TCBInit_publish_enabled with(K:=Kpub);try assumption.
     * pose proof(Int.unsigned_range off);lia.
     * unfold V293_prio_row. destruct(p <? 8);lia.
     * unfold V293_prio_bit. destruct(p <? 8)eqn:E;apply Nat.ltb_lt in E||apply Nat.ltb_ge in E;lia.
     * apply V293_tcb_publication_caller_frame_good;exact Frame.
     * apply V293_tcb_publication_caller_frame_linv;exact HR.
     * intros. eapply Capacity;eassumption.
     * intros s H. apply Return with(b:=b)(off:=off). eapply V293_tcb_full_publication_restore;exact H.
Qed.
Print Assumptions V293_OS_TCBInit_free_body_published.
